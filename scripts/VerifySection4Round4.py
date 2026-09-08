"""Check the unchanged third Section 4 baseline, rebuild round four, and audit all declarations.

Run from any directory with --lean PATH and --dependencies PATH. The dependency
directory contains the pinned mathlib and its dependency packages. Historical
verification files are read as evidence, never rewritten.
"""

from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
import argparse
import hashlib
import json
import os
import re
import subprocess
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--lean", required=True)
parser.add_argument("--dependencies", required=True)
args = parser.parse_args()
project = Path(__file__).resolve().parents[1]
lean = Path(args.lean).resolve()
dependencies = Path(args.dependencies).resolve()
build = project / ".lake/build/lib/lean"
logs = project / ".lake/build/section4-round4-verification"
logs.mkdir(parents=True, exist_ok=True)
baseline = json.loads((project / "verification-section4-round3.json").read_text(encoding="utf-8-sig"))
modules = re.findall(r"^import BoundedUncertainty\.(\w+)\s*$",
                     (project / "BoundedUncertainty.lean").read_text(encoding="utf-8-sig"), re.M)
assert len(modules) == len(set(modules))
assert set(modules) == {p.stem for p in (project / "BoundedUncertainty").glob("*.lean")}
sources = {name: project / "BoundedUncertainty" / (name + ".lean") for name in modules}
hashes = {name: hashlib.sha256(path.read_bytes()).hexdigest().upper() for name, path in sources.items()}
completed = set()
for row in baseline["sources"]:
    assert hashes[row["module"]] == row["sha256"], row["module"]
    assert (build / "BoundedUncertainty" / (row["module"] + ".olean")).is_file()
    completed.add(row["module"])
baseline_modules = sorted(completed)
new_modules = [name for name in modules if name not in completed]
imports = {name: set(re.findall(r"^import BoundedUncertainty\.(\w+)\s*$",
                              path.read_text(encoding="utf-8-sig"), re.M))
           for name, path in sources.items()}
freeze = [{"module": name, "sha256": hashes[name],
           "lines": len(sources[name].read_text(encoding="utf-8-sig").splitlines())}
          for name in modules]
(project / "verification-section4-round4-source-freeze.json").write_text(
    json.dumps(freeze, indent=2) + "\n", encoding="utf-8")
audit_text = (project / "AxiomAudit.lean").read_text(encoding="utf-8-sig")
assert all(not line.strip() or line == "import BoundedUncertainty" or
           re.fullmatch(r"#print axioms \S+", line) for line in audit_text.splitlines())
names = re.findall(r"^#print axioms (\S+)$", audit_text, re.M)
assert len(names) == len(set(names))


def strip_comments(text):
    """Erase nested Lean comments and strings while preserving line boundaries."""
    output, depth, quoted, index = [], 0, False, 0
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                output.extend("  ")
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif quoted:
            output.append(" ")
            if text[index] == "\\":
                output.append(" ")
                index += 2
            else:
                if text[index] == '"':
                    quoted = False
                index += 1
        elif text.startswith("/-", index):
            depth = 1
            output.extend("  ")
            index += 2
        elif text.startswith("--", index):
            end = text.find("\n", index)
            if end == -1:
                end = len(text)
            output.extend(" " * (end - index))
            index = end
        elif text[index] == '"':
            quoted = True
            output.append(" ")
            index += 1
        else:
            output.append(text[index])
            index += 1
    assert depth == 0 and not quoted
    return "".join(output)


source_names = []
for name, path in sources.items():
    stripped = strip_comments(path.read_text(encoding="utf-8-sig"))
    # These guards make the declaration extractor fail closed if the project
    # starts using a declaration form or namespace convention it does not handle.
    assert re.findall(r"^namespace\s+(\S+)", stripped, re.M) == ["BoundedUncertainty"], name
    assert not re.search(r"^\s*(?:private|protected|opaque|instance)\b", stripped, re.M), name
    assert not re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", stripped), name
    declarations = re.findall(r"^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:def|theorem|lemma|structure|abbrev)\s+([^\s(:]+)", stripped, re.M)
    assert declarations, name
    source_names.extend("BoundedUncertainty." + declaration for declaration in declarations)
assert len(source_names) == len(set(source_names)) == len(names)
assert set(source_names) == set(names), (set(source_names) - set(names), set(names) - set(source_names))
root_hash = hashlib.sha256((project / "BoundedUncertainty.lean").read_bytes()).hexdigest()
audit_hash = hashlib.sha256((project / "AxiomAudit.lean").read_bytes()).hexdigest()
env = os.environ.copy()
env["LEAN_PATH"] = ";".join([str(build)] + [str(p / ".lake/build/lib/lean")
    for p in dependencies.iterdir() if (p / ".lake/build/lib/lean").is_dir()])
flags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
records = []
started_at = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
version = subprocess.run([str(lean), "--version"], stdout=subprocess.PIPE,
    stderr=subprocess.STDOUT, encoding="utf-8", creationflags=flags)
assert version.returncode == 0
assert baseline["leanVersion"] in version.stdout and baseline["leanCommit"] in version.stdout


def check_output(result, output, label):
    assert result == 0, (label, result, output)
    assert not re.search(r": (?:error(?:\([^\n]*\))?|warning):", output), (label, output)
    assert "sorryAx" not in output, label


def run_module(name):
    temporary = logs / (name + ".olean")
    result = subprocess.run([str(lean), "-o", str(temporary), str(sources[name])],
        cwd=project, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        encoding="utf-8", creationflags=flags)
    (logs / (name + ".txt")).write_text(result.stdout, encoding="utf-8")
    check_output(result.returncode, result.stdout, name)
    assert hashlib.sha256(sources[name].read_bytes()).hexdigest().upper() == hashes[name]
    os.replace(temporary, build / "BoundedUncertainty" / (name + ".olean"))
    return name


with ThreadPoolExecutor(max_workers=3) as executor:
    pending = list(new_modules)
    running = {}
    while pending or running:
        for name in list(pending):
            if len(running) >= 3:
                break
            if imports[name] <= completed:
                running[executor.submit(run_module, name)] = name
                pending.remove(name)
        assert running or not pending, ("Dependency cycle", pending)
        ready = [future for future in running if future.done()]
        for future in ready:
            name = future.result()
            completed.add(name)
            del running[future]
            records.append("Compiled added module: BoundedUncertainty." + name + " (exit 0; no warnings)")
            print(records[-1], flush=True)
        time.sleep(0.1)

root = subprocess.run([str(lean), "-o", str(build / "BoundedUncertainty.olean"), "BoundedUncertainty.lean"],
    cwd=project, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    encoding="utf-8", creationflags=flags)
check_output(root.returncode, root.stdout, "entry point")
print("Project entry point compiled (exit 0; no warnings).", flush=True)


def audit_chunk(index):
    expected = names[index::3]
    source = project / f"verification-section4-round4-axioms-{index + 1}-input.lean"
    source.write_text("import BoundedUncertainty\n\n" +
        "\n".join("#print axioms " + name for name in expected) + "\n", encoding="utf-8")
    result = subprocess.run([str(lean), str(source)], cwd=project, env=env,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding="utf-8", creationflags=flags)
    (project / f"verification-section4-round4-axioms-{index + 1}-output.txt").write_text(result.stdout, encoding="utf-8")
    check_output(result.returncode, result.stdout, f"audit group {index + 1}")
    reported = re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)", result.stdout)
    assert len(reported) == len(expected) and set(reported) == set(expected)
    for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout):
        assert {a.strip() for a in group.split(",") if a.strip()} <= {"propext", "Classical.choice", "Quot.sound"}
    print(f"Axiom group {index + 1} passed: {len(expected)} declarations.", flush=True)
    return index, result.stdout


with ThreadPoolExecutor(max_workers=3) as executor:
    outputs = dict(executor.map(audit_chunk, range(3)))
for name, path in sources.items():
    assert hashlib.sha256(path.read_bytes()).hexdigest().upper() == hashes[name], name
assert hashlib.sha256((project / "BoundedUncertainty.lean").read_bytes()).hexdigest() == root_hash
assert hashlib.sha256((project / "AxiomAudit.lean").read_bytes()).hexdigest() == audit_hash
header = (f"Section 4 round four incremental verification started {started_at}.\n"
          f"All {len(baseline_modules)} baseline source hashes match the preserved baseline.\n"
          "Baseline modules use their previously verified compiled objects; they were not freshly rebuilt in this run.\n"
          f"Every one of the {len(new_modules)} added modules was freshly rebuilt in dependency order.\n")
(project / "verification-section4-round4.txt").write_text(header + "\n".join(records) +
    "\nProject entry point compiled (exit 0; no warnings).\n" +
    "All current named declarations audited in three disjoint groups with identical root import.\n" +
    "\n".join(outputs[i] for i in range(3)) +
    "Axiom audit passed: only propext, Classical.choice and Quot.sound were used.\n", encoding="utf-8")
result = {"verifiedAtUtc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
          "moduleCount": len(modules), "sourceLineCount": sum(row["lines"] for row in freeze),
          "auditedDeclarationCount": len(names), "addedModules": new_modules,
          "unchangedBaselineModuleCount": len(baseline_modules), "buildExitCode": 0,
          "axiomAuditExitCode": 0, "warningsFound": False,
          "permittedAxioms": ["propext", "Classical.choice", "Quot.sound"], "sources": freeze}
(logs / "result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(f"Verified {len(new_modules)} added modules and {len(names)} total named declarations.", flush=True)
