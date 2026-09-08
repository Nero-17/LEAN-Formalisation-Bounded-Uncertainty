"""Guarded inventory of handwritten Lean declarations in this repository.

Named instances and nested namespaces are supported for the licensed Sperner
foundation. Compiler-generated declarations are dependencies of the named
declarations, not separately counted as handwritten source declarations.
"""

import re


def strip_comments(text):
    """Erase nested comments and strings, preserving line boundaries."""
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
            output.append("\n" if text[index] == "\n" else " ")
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
    assert depth == 0 and not quoted, "Unterminated comment or string"
    return "".join(output)


def declarations(text):
    """Return (fully qualified name, kind), rejecting unsupported declarations."""
    stripped = strip_comments(text)
    assert not re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", stripped)
    assert not re.search(r"^\s*(?:private|protected|opaque|class|mutual)\b", stripped, re.M)
    stack, result = [], []
    for line in stripped.splitlines():
        line = line.strip()
        scope = re.fullmatch(r"(namespace|section)\s*(\S+)?", line)
        if scope:
            kind, name = scope.groups()
            assert kind != "namespace" or name
            stack.append((kind, name))
            continue
        if line == "noncomputable section":
            stack.append(("section", None))
            continue
        end = re.fullmatch(r"end(?:\s+(\S+))?", line)
        if end:
            assert stack, "Unmatched end"
            kind, name = stack.pop()
            assert end[1] is None or end[1] == name, (end[1], name)
            continue
        line = re.sub(r"^(?:@\[[^\]\n]*\]\s*)+", "", line)
        match = re.match(r"^(?:noncomputable\s+)?(def|theorem|lemma|structure|abbrev|instance)\s+([^\s(:{\[]+)", line)
        if match:
            kind, name = match.groups()
            assert re.fullmatch(r"[\w'.]+", name), (kind, name)
            namespace = ".".join(name for kind, name in stack if kind == "namespace")
            assert namespace == "BoundedUncertainty" or namespace.startswith("BoundedUncertainty."), namespace
            result.append((namespace + "." + name, kind))
        else:
            assert not re.match(r"^(?:noncomputable\s+)?(?:def|theorem|lemma|structure|abbrev|instance)\b", line), line
    assert not stack, stack
    assert result and len(result) == len(set(name for name, _ in result))
    return result
