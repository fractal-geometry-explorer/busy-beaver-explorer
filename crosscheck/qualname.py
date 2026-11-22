"""Print the module-qualified name of the last 'Theorem/Lemma halt|nonhalt' in a .v file (tracks Module/End)."""
import re, sys
src = open(sys.argv[1]).read()
src = re.sub(r"\(\*.*?\*\)", "", src, flags=re.S)  # comments are not nested in these files' headers
stack, last = [], None
for line in src.splitlines():
    s = line.strip()
    m = re.match(r"Module\s+(?!Type)(\w+)(.*)", s)
    if m and ":=" not in m.group(2):
        stack.append(("M", m.group(1))); continue
    m = re.match(r"Section\s+(\w+)", s)
    if m:
        stack.append(("S", m.group(1))); continue
    m = re.match(r"End\s+(\w+)\s*\.", s)
    if m and stack and stack[-1][1] == m.group(1):
        stack.pop(); continue
    m = re.match(r"(Theorem|Lemma)\s+(halt|nonhalt)\b", s)
    if m:
        last = ".".join([n for k, n in stack if k == "M"] + [m.group(2)])
print(last)
