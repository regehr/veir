"""Lean exporter regression test; run after `lake build UnitTest.PuddlePrinting`."""

from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import puddle_catalog as catalog


@unittest.skipUnless(shutil.which('lake'), 'Lake is required for the exporter integration test')
class LeanExportTests(unittest.TestCase):
    def test_scan_handles_function_bodies_without_constant_heads(self):
        repo = Path(__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'patterns.jsonl'
            driver = Path(directory) / 'export.lean'
            # This module imports ordinary functions such as intConstantGuard.
            # Their lambda bodies used to panic during the compiled-pattern scan.
            driver.write_text(catalog.make_driver(
                ['Veir.InstSimplify.IS0609'], False, output), encoding='utf-8')
            result = subprocess.run(
                ['lake', 'env', 'lean', '--tstack=400000', str(driver)],
                cwd=repo, capture_output=True, text=True, timeout=90)
            diagnostics = result.stdout + result.stderr
            self.assertEqual(result.returncode, 0, diagnostics)
            # Lean panics can still exit successfully, so inspect diagnostics too.
            self.assertNotIn('PANIC', diagnostics)
            definitions, records = catalog.collect_records([output])
            catalog.validate_catalog(definitions, records)
            self.assertEqual({r['name'] for r in records}, {
                'Veir.InstSimplify.IS0609.pattern',
                'Veir.InstSimplify.IS0609.pattern_left',
            })


if __name__ == '__main__':
    unittest.main()
