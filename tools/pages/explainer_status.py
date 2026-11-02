"""Write the status panel of a machine's explainer page from its status.json.

An explainer page can list every claim of the machine's status.json by what it rests on, as the proof-status page
does, by holding the claims as JSON in a block

  <script type="application/json" id="status-data">
  ...
  </script>

that its own script renders.  After editing status.json run

  python3 tools/pages/explainer_status.py MACHINE_DIR/status.json pages/SHORT/explainer.html

next to tools/pages/build_status.py; `check(status, page)` is what a test calls to see that the page is current.
Taken from `bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/py/explainer_status.py` (which keeps its own copy) with the paths made
arguments.
"""
import json
import re
import sys

BLOCK = re.compile(r'(<script type="application/json" id="status-data">\n)(.*?)(\n</script>)', re.S)


def payload(spec):
    data = {"asof": spec["asof"], "claims": [{k: c.get(k, "") for k in ("level", "title", "text", "where")}
                                             for c in spec["claims"]]}
    return json.dumps(data, ensure_ascii=False, indent=1).replace("</", "<\\/")


def build(page, spec):
    """The page with its status block replaced by the claims of `spec`."""
    m = BLOCK.search(page)
    if not m:
        raise ValueError("no status block in the page")
    return page[:m.start(2)] + payload(spec) + page[m.end(2):]


def check(status_path, page_path):
    """True if the page's status block is the one `status_path` gives."""
    with open(status_path) as f:
        spec = json.load(f)
    with open(page_path) as f:
        page = f.read()
    return build(page, spec) == page


def main(argv):
    if len(argv) != 2:
        print(__doc__)
        return 1
    with open(argv[0]) as f:
        spec = json.load(f)
    with open(argv[1]) as f:
        page = f.read()
    out = build(page, spec)
    if out != page:
        with open(argv[1], "w") as f:
            f.write(out)
    print("wrote" if out != page else "unchanged", argv[1])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
