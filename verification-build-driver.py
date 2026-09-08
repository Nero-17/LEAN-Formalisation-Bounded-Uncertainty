from pathlib import Path
import hashlib, json, os, re, subprocess, time

project = Path(r'C:\Users\lzysh\Documents\Codex\2026-09-07\new-chat\outputs\bounded-uncertainty-lean')
lean = Path(r'C:\Users\lzysh\Documents\Codex\bounded-noise-asymptotic-periodicity\.local-tools\elan-home\toolchains\leanprover--lean4---v4.28.0\bin\lean.exe')
dependencies = Path(r'C:\Users\lzysh\Documents\Codex\bounded-noise-asymptotic-periodicity\.lake\packages')
build = project / '.lake/build/lib/lean'
logs = project / '.lake/build/parallel-logs'
logs.mkdir(parents=True, exist_ok=True)
freeze = {r['module']: r['sha256'] for r in json.loads(Path(r'C:\Users\lzysh\Documents\Codex\2026-09-07\new-chat\work\section3-final-source-freeze.json').read_text(encoding='utf-8-sig'))}
modules = re.findall(r'^import BoundedUncertainty\.(\w+)$', (project / 'BoundedUncertainty.lean').read_text(encoding='utf-8-sig'), re.M)
texts = {name: (project / 'BoundedUncertainty' / (name + '.lean')).read_text(encoding='utf-8-sig') for name in modules}
imports = {name: set(re.findall(r'^import BoundedUncertainty\.(\w+)\s*$', text, re.M)) for name, text in texts.items()}
assert set(modules) == set(freeze)
for name in modules:
    assert hashlib.sha256((project / 'BoundedUncertainty' / (name + '.lean')).read_bytes()).hexdigest().upper() == freeze[name], name
old_log = (project / 'verification.txt').read_text(encoding='utf-8-sig')
assert not re.search(r': (?:error|warning)', old_log)
started = re.findall(r'^Checking BoundedUncertainty\.(\w+)\s*$', old_log, re.M)
assert modules[:len(started)] == started
# In the serial Check.ps1, the next module is announced only after the previous
# Lean invocation returned zero. The interrupted last announcement is not a pass.
completed = set(started[:-1])
assert completed
cut = old_log.rfind('Checking BoundedUncertainty.' + started[-1])
prefix = old_log[:cut]
verification = (project / 'verification.txt').open('w', encoding='utf-8', newline='\n')
verification.write(prefix)
verification.flush()
def emit(message):
    print(message, flush=True)
    verification.write(message + '\n')
    verification.flush()
emit(f'Continuation: {len(completed)} serial modules passed before interruption; every remaining module is rebuilt in dependency order with up to 3 independent Lean processes.')
env = os.environ.copy()
env['LEAN_PATH'] = ';'.join([str(build)] + [str(p / '.lake/build/lib/lean') for p in dependencies.iterdir() if (p / '.lake/build/lib/lean').is_dir()])
running = {}
pending = [name for name in modules if name not in completed]
flags = subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0
try:
    while pending or running:
        for name in list(pending):
            if len(running) >= 3:
                break
            if not imports[name] <= completed:
                continue
            output = logs / (name + '.txt')
            stream = output.open('wb')
            temporary = logs / (name + '.olean')
            emit('Checking BoundedUncertainty.' + name)
            process = subprocess.Popen([str(lean), '-o', str(temporary), str(Path('BoundedUncertainty') / (name + '.lean'))], cwd=project, env=env, stdout=stream, stderr=subprocess.STDOUT, creationflags=flags)
            running[name] = (process, stream, output, temporary)
            pending.remove(name)
        if not running and pending:
            raise RuntimeError('Dependency cycle or missing completed dependency: ' + repr(pending))
        for name, (process, stream, output, temporary) in list(running.items()):
            result = process.poll()
            if result is None:
                continue
            stream.close()
            diagnostic = output.read_text(encoding='utf-8-sig')
            if diagnostic:
                emit(diagnostic.rstrip())
            if result != 0 or re.search(r': (?:error(?:\([^\n]*\))?|warning):', diagnostic):
                raise RuntimeError(f'{name} failed strict compilation, exit {result}')
            assert hashlib.sha256((project / 'BoundedUncertainty' / (name + '.lean')).read_bytes()).hexdigest().upper() == freeze[name], name
            os.replace(temporary, build / 'BoundedUncertainty' / (name + '.olean'))
            completed.add(name)
            del running[name]
            emit(f'Completed {len(completed)}/{len(modules)}: BoundedUncertainty.{name}')
        time.sleep(0.2)
    for arguments in [['-o', str(build / 'BoundedUncertainty.olean'), 'BoundedUncertainty.lean'], ['AxiomAudit.lean']]:
        result = subprocess.run([str(lean)] + arguments, cwd=project, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding='utf-8', creationflags=flags)
        output = result.stdout
        if output:
            emit(output.rstrip())
        if result.returncode != 0 or re.search(r': (?:error(?:\([^\n]*\))?|warning):', output):
            raise RuntimeError('Entry or axiom audit compilation failed')
        if arguments == ['AxiomAudit.lean']:
            (project / '.lake/build/axiom-audit.txt').write_text(output, encoding='utf-8')
            expected = re.findall(r'^#print axioms (\S+)$', (project / 'AxiomAudit.lean').read_text(encoding='utf-8-sig'), re.M)
            for name in expected:
                assert re.search("'" + re.escape(name) + "' (?:depends on axioms:|does not depend on any axioms)", output), name
            assert 'sorryAx' not in output
            for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output):
                assert {a.strip() for a in group.split(',') if a.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}, group
    emit('Axiom audit passed: only propext, Classical.choice and Quot.sound were used.')
finally:
    for process, stream, _, _ in running.values():
        if process.poll() is None:
            process.terminate()
            process.wait()
        stream.close()
    verification.close()
