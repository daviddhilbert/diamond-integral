#!/usr/bin/env python3
"""Audit the corrected pins, exact dependency layers and measured-zero interfaces.

Run after the five section verifiers. This is a compatibility audit, not a
producer for the four conditional Gamma-valued lifting/kernel interfaces.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification/upstream-weighted-zero-upgrade'
PINS = {
    'special_transformations': '423c767a84b709487da7e798f70f0639545db1ac',
    'integration_in_acvf': 'ab4c0e8b15e1e21b0b4fce57eed764be76020e06',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
SPECIAL = 'SpecialTransformations.Section10.'
LOCAL = 'DiamondIntegral.'
NAMES = [SPECIAL + n for n in [
    'WeightedZero.iso_iff', 'MeasuredRVZero.lift_weight',
    'MeasuredRVZero.liftMap_labels', 'MeasuredRVZero.liftMap_measure',
    'theorem_10_4_gamma_zero', 'theorem_10_5_gamma_zero', 'corollary_10_6_gamma_zero',
    'ZeroForm.gammaProduct_weight', 'gammaZeroForm_weight_eq_iff',
]] + [LOCAL + n for n in [
    'Section3.YinMeasuredLiftInput',
    'Section3.YinDegreeMeasuredLiftInput',
    'Section3.YinGammaGroundMeasuredLiftInput',
    'Section3.YinGammaGroundDegreeMeasuredLiftInput',
    'Section3.MeasuredRVObject.product_combinedWeight',
    'Section3.MeasuredVFData.product_form',
    'Section3.GammaGroundMeasuredRVObject.zero_combinedWeight',
    'Section3.GammaGroundMeasuredRVObject.product_combined',
    'Section3.GammaGroundMeasuredVFData.product_form',
    'Section3.gammaGroundZeroMeasuredRVToVF',
    'Section3.gammaGroundZeroMeasuredRVToVF_faithful',
    'Section3.gammaGroundZeroMeasuredRVToVF_full',
    'Section3.gammaGroundMeasuredNativeTensor_rank_zero_absorption',
    'Section4.RESWeightEmbedding.weightMap_injective',
    'Section4.RESWeightEmbedding.reducedWeightMap_injective',
    'Section4.RESWeightEmbedding.radiusWeightMap_injective',
    'Section4.RVZeroWeightedCount.res_weightedUnit',
    'Section4.VariableApertureMeasuredComparison.relation_formula',
    'Section4.VariableApertureMeasuredComparison.functional_ideal_maps_into_p',
    'Section4.RelativeAnnularQuotient.quotient_injective_on_degree_zero',
    'Section4.RelativeAnnularQuotient.evaluation_res',
    'Section5.completed_section5_input',
    'Section5.completed18GroundLiftInput',
    'Section6.proposition_6_19_vfGenerated',
    'Section6.lemma_6_27',
    'Section6.lemma_6_31_zero_arity',
    'Section6.lemma_6_14_bounded_variable_apertures',
    'Section6.lemma_6_38_bounded_variable_apertures',
]]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args, log):
    with (OUT / log).open('w') as f:
        subprocess.run(args, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT, check=True)


def main():
    OUT.mkdir(exist_ok=True)
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    configured = {p['name']: p['rev'] for p in manifest['packages']}
    layers = {}
    for package, revision in PINS.items():
        directory = ROOT / '.lake/packages' / package
        actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=directory, text=True).strip()
        if configured[package] != revision or actual != revision:
            raise SystemExit(f'Pin mismatch: {package}')
        dirty = set()
        for args in [['git', 'diff', '--name-only', '-z'],
                     ['git', 'ls-files', '--others', '--exclude-standard', '-z']]:
            dirty.update(x for x in subprocess.check_output(args, cwd=directory).decode().split('\0') if x)
        expected = set()
        if package == 'integration_in_acvf':
            record = json.loads((ROOT / 'section 5/reference/integration-section6-scope-adapter.json').read_text())
            expected = set(record['files'])
            for name, identity in record['files'].items():
                if sha(directory / name) != identity:
                    raise SystemExit(f'Scope adapter mismatch: {name}')
        if dirty != expected:
            raise SystemExit(f'Unexpected dependency layer: {package}: {sorted(dirty ^ expected)}')
        layers[package] = {'revision': revision, 'local_files': sorted(dirty)}
    run(['python3', 'section 5/prepare-dependencies.py', '--check'], 'prepared-sources.log')
    sections = {}
    for n in range(2, 7):
        relative = f'section {n}/verification/' + ('VERIFICATION.json' if n == 3 else 'status.json')
        p = ROOT / relative
        data = json.loads(p.read_text())
        expected_status = 'PASS_SECTION5_REQUESTED_SCOPE_IN_RECORDED_CONTEXT' if n == 5 else 'PASS'
        if data['status'] != expected_status:
            raise SystemExit(f'Section {n} did not pass')
        # Older Section 4 receipts bind revisions through the manifest hash.
        sources = data.get('sources', data.get('source_sha256', {}))
        manifest_matches = sources.get('lake-manifest.json') == sha(ROOT / 'lake-manifest.json')
        if not manifest_matches and not all(revision in p.read_text() for revision in PINS.values()):
            raise SystemExit(f'Stale dependency receipt: {relative}')
        checked = 0
        for name, identity in sources.items():
            if name.startswith(f'section {n}/') and name.endswith('.lean'):
                if sha(ROOT / name) != identity:
                    raise SystemExit(f'Stale proof source: {name}')
                checked += 1
        if not checked:
            raise SystemExit(f'Missing source hashes: {relative}')
        sections[str(n)] = {'receipt': relative, 'status': data['status'], 'sha256': sha(p), 'checked_Lean_sources': checked}
    run(['lake', 'build', 'Section10.WeightedZeroResults', 'Section10.WeightedFormProducts'], 'weighted-upstream-build.log')
    audit = OUT / 'Audit.lean'
    audit.write_text('import DiamondIntegral\nimport Section10.WeightedZeroResults\n'
                     'import Section10.WeightedFormProducts\nset_option pp.universes true\n'
                     'set_option pp.fullNames true\n' + '\n'.join(
                         f'#check @{name}\n#print {name}\n#print axioms {name}' for name in NAMES) + '\n')
    run(['lake', 'env', 'lean', str(audit.relative_to(ROOT))], 'types-and-axioms.log')
    output = (OUT / 'types-and-axioms.log').read_text()
    principles = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", output):
        used = {x.strip() for x in re.sub(r'\.\{[^}]*\}', '', raw).split(',') if x.strip()}
        if not used <= ALLOWED:
            raise SystemExit(f'Unexpected axioms: {name}: {used - ALLOWED}')
        principles[name] = sorted(used)
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        principles[name] = []
    if set(principles) != set(NAMES) or 'sorryAx' in output:
        raise SystemExit('Incomplete measured compatibility type/axiom audit')
    report = {
        'status': 'PASS', 'pins': PINS, 'dependency_layers': layers, 'sections': sections,
        'interfaces': principles,
        'scope': 'New-pin source/type/axiom compatibility for Sections 2–6, weighted finite zero families, mixed products, exact zero lifts, RES/tensor coefficients and relative-aperture comparisons. No manuscript statement or proof body changed in this migration.',
        'conditional_inputs': ['YinMeasuredLiftInput', 'YinDegreeMeasuredLiftInput',
                               'YinGammaGroundMeasuredLiftInput', 'YinGammaGroundDegreeMeasuredLiftInput'],
        'conditional_scope': 'These existing Gamma-valued kernel inputs remain precise accepted cited inputs. The corrected upstream Section 7 HK kernel uses RV-valued forms and is not an unconditional producer for them. No general Gamma-to-RV section or kernel coarsening is assumed.',
        'downstream': 'This audit does not prove this paper\'s revised Section 7 kernel or Section 8 specialization.',
        'evidence': {p.name: sha(p) for p in OUT.iterdir() if p.name not in {'status.json', 'verification-run.json', 'compatibility-verifier.log'} and p.is_file()},
        'script_sha256': sha(Path(__file__)),
    }
    (OUT / 'status.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(f'PASS: corrected pins, Sections 2–6 receipts and {len(NAMES)} measured compatibility interfaces; cited Gamma kernel inputs remain explicit.')


if __name__ == '__main__':
    main()
