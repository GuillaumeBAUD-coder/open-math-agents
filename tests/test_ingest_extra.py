"""Exercise Wikipedia citation handling through the catalogue importer's CLI."""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class WikipediaImportTest(unittest.TestCase):
    def test_citations_and_published_ids(self):
        fixture = """== Unsolved problems ==
=== Logic ===
* Determine the structure of Keisler's order.<ref>Changed citation.</ref>
* Fresh question: Does the example hold?<ref>See
  [[Example Journal]].</ref>
* <ref>[[Journal name]]</ref>[[Example subject]]: Can X<ref name="citation"
  >[[Editor]]</ref> be constructed?<ref name="citation" />
== Problems solved since 2015 ==
== See also ==
"""
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            (work / "unsolved").write_text(fixture)
            (work / "conjectures").write_text(
                "==Open problems==\n==Conjectures now proved==\n==Refutations of conventional"
            )
            (work / "erdos").write_text("")
            output = work / "extra.json"
            subprocess.run([
                sys.executable, "-I", str(ROOT / "scripts" / "ingest_extra.py"),
                work / "unsolved", work / "conjectures", work / "opg", work / "erdos", output,
            ], check=True, stdout=subprocess.DEVNULL)
            problems = {p["id"]: p for p in json.loads(output.read_text())["problems"]}
        self.assertEqual(set(problems), {"wp-advances-in-mathematics", "wp-fresh-question", "wp-example-subject"})
        self.assertEqual(problems["wp-advances-in-mathematics"]["title"], "Structure of Keisler's order")
        self.assertEqual(problems["wp-fresh-question"]["statement"], "Does the example hold?")
        self.assertTrue(problems["wp-fresh-question"]["ref"].endswith("List_of_unsolved_problems_in_mathematics#Logic"))
        self.assertEqual(problems["wp-example-subject"]["statement"], "Can X be constructed?")
        self.assertEqual(problems["wp-example-subject"]["ref"], "https://en.wikipedia.org/wiki/Example_subject")


if __name__ == "__main__":
    unittest.main()
