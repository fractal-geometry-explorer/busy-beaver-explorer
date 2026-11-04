"""Write the status panel of pages/1RB1RA_1RC1LB_1LD0RA_1LB0LE/explainer.html from status.json.

The explainer's last part lists every claim of status.json by what it rests on, as the proof-status page does. The
claims sit in the page as JSON (`<script type="application/json" id="status-data">`), so after editing status.json run

  python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/py/explainer_status.py

next to tools/pages/build_status.py; tests/test_explainer.py checks that the page is current.
"""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REPO = os.path.dirname(ROOT)
STATUS = os.path.join(ROOT, "status.json")
PAGE = os.path.join(REPO, "pages", "1RB1RA_1RC1LB_1LD0RA_1LB0LE", "explainer.html")
BLOCK = re.compile(r'(<script type="application/json" id="status-data">\n)(.*?)(\n</script>)', re.S)


def payload(spec):
    data = {"asof": spec["asof"], "claims": [{k: c[k] for k in ("level", "title", "text", "where")}
                                             for c in spec["claims"]]}
    return json.dumps(data, ensure_ascii=False, indent=1).replace("</", "<\\/")


def build(page, spec):
    m = BLOCK.search(page)
    if not m:
        raise ValueError("no status block in the page")
    return page[:m.start(2)] + payload(spec) + page[m.end(2):]


def main():
    with open(STATUS) as f:
        spec = json.load(f)
    with open(PAGE) as f:
        page = f.read()
    out = build(page, spec)
    if out != page:
        with open(PAGE, "w") as f:
            f.write(out)
    print("wrote" if out != page else "unchanged", PAGE)


if __name__ == "__main__":
    main()
