from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib, json, os, re, subprocess, threading

project = Path(r'C:\Users\lzysh\Documents\Codex\2026-09-07\new-chat\outputs\bounded-uncertainty-lean')
lean = Path(r'C:\Users\lzysh\Documents\Codex\bounded-noise-asymptotic-periodicity\.local-tools\elan-home\toolchains\leanprover--lean4---v4.28.0\bin\lean.exe')
dependencies = Path(r'C:\Users\lzysh\Documents\Codex\bounded-noise-asymptotic-periodicity\.lake\packages')
build = project / '.lake/build/lib/lean'
chunk_dir = project / '.lake/build/audit-chunks'
chunk_dir.mkdir(parents=True, exist_ok=True)
freeze = json.loads((project / 'verification-source-freeze.json').read_text(encoding='utf-8-sig'))
for row in freeze:
    assert hashlib.sha256((project / 'BoundedUncertainty' / (row['module'] + '.lean')).read_bytes()).hexdigest().upper() == row['sha256']
audit_lines = (project / 'AxiomAudit.lean').read_text(encoding='utf-8-sig').splitlines()
assert all(not line.strip() or line == 'import BoundedUncertainty' or re.fullmatch(r'#print axioms \S+', line) for line in audit_lines)
names = [line.removeprefix('#print axioms ') for line in audit_lines if line.startswith('#print axioms ')]
assert len(names) == len(set(names)) == 510
prior_log = (project / 'verification.txt').read_text(encoding='utf-8-sig')
assert 'Completed 69/69:' in prior_log and 'Axiom audit passed:' not in prior_log
assert not re.search(r': (?:error|warning)', prior_log)
assert (build / 'BoundedUncertainty.olean').is_file()
env = os.environ.copy()
env['LEAN_PATH'] = ';'.join([str(build)] + [str(p / '.lake/build/lib/lean') for p in dependencies.iterdir() if (p / '.lake/build/lib/lean').is_dir()])
flags = subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0
lock = threading.Lock()
reported = set()
processes = []
def run_chunk(index):
    expected = names[index::3]
    source = chunk_dir / f'AxiomAudit{index}.lean'
    source.write_text('import BoundedUncertainty\n\n' + '\n'.join('#print axioms ' + name for name in expected) + '\n', encoding='utf-8')
    process = subprocess.Popen([str(lean), str(source)], cwd=project, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, encoding='utf-8', creationflags=flags)
    with lock:
        processes.append(process)
    output = []
    with (chunk_dir / f'AxiomAudit{index}.txt').open('w', encoding='utf-8') as capture:
        for line in process.stdout:
            output.append(line)
            capture.write(line)
            capture.flush()
            match = re.match(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)", line)
            if match:
                with lock:
                    assert match[1] in expected and match[1] not in reported
                    reported.add(match[1])
                    if len(reported) % 30 == 0 or len(reported) == len(names):
                        print(f'Axiom reports received: {len(reported)}/{len(names)}', flush=True)
    result = process.wait()
    output = ''.join(output)
    assert result == 0, (index, result, output)
    assert not re.search(r': (?:error(?:\([^\n]*\))?|warning):', output), output
    assert 'sorryAx' not in output
    for name in expected:
        assert re.search("'" + re.escape(name) + "' (?:depends on axioms:|does not depend on any axioms)", output), name
    for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output):
        assert {a.strip() for a in group.split(',') if a.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}, group
    print(f'Axiom chunk {index + 1}/3 passed: {len(expected)} declarations', flush=True)
    return index, output
results = {}
try:
    with ThreadPoolExecutor(max_workers=3) as executor:
        futures = [executor.submit(run_chunk, index) for index in range(3)]
        for future in as_completed(futures):
            index, output = future.result()
            results[index] = output
    assert reported == set(names)
    for row in freeze:
        assert hashlib.sha256((project / 'BoundedUncertainty' / (row['module'] + '.lean')).read_bytes()).hexdigest().upper() == row['sha256']
    output = '\n'.join(results[index].rstrip() for index in range(3)) + '\n'
    (project / '.lake/build/axiom-audit.txt').write_text(output, encoding='utf-8')
    with (project / 'verification.txt').open('a', encoding='utf-8') as verification:
        verification.write('Axiom audit continuation: the project entry already compiled successfully; all 510 independent #print axioms commands from AxiomAudit.lean were compiled in three disjoint round-robin chunks, with identical import context.\n')
        verification.write(output)
        verification.write('Axiom audit passed: only propext, Classical.choice and Quot.sound were used.\n')
    print('Axiom audit passed: only propext, Classical.choice and Quot.sound were used.', flush=True)
finally:
    for process in processes:
        if process.poll() is None:
            process.terminate()
            process.wait()
