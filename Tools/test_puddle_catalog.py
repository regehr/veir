"""Catalog coverage and PDF completeness checks; no Lean/PDF tools required."""

from pathlib import Path
import tempfile
import unittest

import puddle_catalog as catalog


class DiscoveryTests(unittest.TestCase):
    def test_inferred_aliases_and_nested_comments(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            sources = {
                'Rules': 'import Veir.PatternRewriter.Puddle\ndef rule : Pattern OpCode := builder',
                'Alias': 'module\npublic import all Veir.Rules\ndef alias := rule',
                'AliasAgain': 'import Veir.Alias\nabbrev another := alias',
                'Barrel': 'import Veir.Rules',
                'ViaBarrel': 'import Veir.Barrel\ndef indirect := rule',
                'Unrelated': 'import Veir.PatternRewriter.Puddle\ndef unrelated := 1',
                'Commented': '''/- Pattern /- nested -/ still a comment -/
                    -- def bogus : Pattern OpCode
                    def message := "Pattern \\" quoted"
                ''',
                'PatternRewriter/Library': 'def library : Pattern OpCode := builder',
            }
            for name, text in sources.items():
                path = repo / 'Veir' / (name + '.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding='utf-8')
            self.assertEqual(catalog.discover_modules(repo), {
                'Veir.Alias': True, 'Veir.AliasAgain': False, 'Veir.Barrel': False,
                'Veir.Rules': False, 'Veir.ViaBarrel': False,
            })


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.definitions = [{'name': 'family'}, {'name': 'alias'}]
        self.record = {
            'name': 'alias', 'families': ['family'],
            'output': 'llvm: (X + 0)  =>  X\nwhere\n  X : T0\n  require width > 0',
        }

    def test_alias_can_cover_its_builder(self):
        catalog.validate_catalog(self.definitions, [self.record])

    def test_new_uncovered_declaration_fails(self):
        with self.assertRaisesRegex(catalog.CatalogError, 'Uncovered.*\n  new_family'):
            catalog.validate_catalog(self.definitions + [{'name': 'new_family'}], [self.record])

    def test_rendering_errors_fail_even_if_name_is_covered(self):
        bad = dict(self.record, error='symbolic graph shape')
        with self.assertRaisesRegex(catalog.CatalogError, '1 pattern renderings failed'):
            catalog.validate_catalog(self.definitions, [bad])

    def test_summary_without_conditions_fails(self):
        bad = dict(self.record, output='llvm: (X + 0)  =>  X')
        with self.assertRaisesRegex(catalog.CatalogError, 'Incomplete rendering'):
            catalog.validate_catalog(self.definitions, [bad])


class PDFTextTests(unittest.TestCase):
    markdown = '''```text
llvm: (X + 0)  =>  X
where
  X : T0
  require width > 0
```
'''
    extracted = '''VeIR · Puddle rewrite catalog
llvm: (X + 0) => X
where
  X : T0

                            1
\fVeIR · Puddle rewrite catalog
  require width > 0

                            2
\f'''

    def test_complete_block_split_across_pages(self):
        catalog.verify_pdf_text(self.markdown, self.extracted)

    def test_lost_condition_fails(self):
        with self.assertRaisesRegex(catalog.CatalogError, 'code block 1'):
            catalog.verify_pdf_text(self.markdown, self.extracted.replace('require width > 0', ''))

    def test_missing_duplicate_rewrite_fails(self):
        with self.assertRaisesRegex(catalog.CatalogError, 'expected 2'):
            catalog.verify_pdf_text(self.markdown * 2, self.extracted)


if __name__ == '__main__':
    unittest.main()
