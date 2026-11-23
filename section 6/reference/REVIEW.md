# Section 6 applied revision and verification

Definition 6.11 and Lemma 6.38 are revised together. The aperture is an
actual original-base nonzero RV function on the complete retained labels,
with nonnegative valuation bounded by one named finite value. Every
bijective lift includes an actual continuous inactive-variable VF endpoint
with the required leading term. No arbitrary RV-to-VF section is assumed.

Every change responds to this aperture revision. Remark 6.12 compares
apertures pointwise; 6.14 proves proper homeomorphism and the approved
almost-everywhere unit total Jacobian for the enlarged class. Existence
results including 6.19 retain their proved constant-aperture witnesses,
which remain admissible with identical maps. Revised 6.38 constructs both
actual finite preparations, the literal conjugate, an RV bijection and the
volume identity at every label, with arbitrary retained RV fibres.

The native exports are
`DiamondIntegral.Section6.lemma_6_14_bounded_variable_apertures` and
`DiamondIntegral.Section6.lemma_6_38_bounded_variable_apertures`.
The earlier complete numbered results remain exported by `Section.lean`.
Precise standing model, smallness, saturation, original-base and
Gamma-affine hypotheses remain explicit in their types.

## Necessary upstream changes

Section 4 now owns the independent relative annular ideal and its actual
ordinary ray cancellation, homogeneous grading, degree-zero preservation,
full measured comparison into (P), and graded quotient with the existing
Euler evaluations and unchanged residue restrictions. Its scalar ideal
and intrinsic RV tensor presentation remain distinct and intact.
The introduction's bounded-integral target and diagrams use the relative
ideal. Sections 2, 3 and 5 need no aperture-dependent manuscript edits.

The completed approved Section 5 snapshot at
`cc8cc35f2a12ea23fb93c5613e24a1a4d9cf7f49` is the upstream baseline.
Its sources and verified dependency overlays are preserved. The Section 6
commit is based on that revision. No Section 7 or 8 main text is changed.
The root build and GitHub Actions now include Section 6.

## Verification

The fresh integrated Sections 2–6 audits passed. At the time of this review
Section 4 checked 5069 public declarations and Section 6 checked 5103
complete public declaration types and transitive axiom records (the current
receipts list 5721 and 5867). Only `propext`, `Classical.choice` and
`Quot.sound` occur. Receipts retain exact source hashes and package pins.
See `../verification/aperture-revision/integrated-audits.json` and each
section's own verification receipt. A declaration count is not a proof of
the Section 7 kernel or Section 8 specialization.

From the repository root, prepare the exact dependencies with
`python3 'section 5/prepare-dependencies.py'`, then run `lake build` and
`lake env python3 'section 6/verify.py'`. The CI workflow also runs the
upstream Section 2–5 audits.

## Downstream handoff

`downstream-handoff.txt` records the synchronized 7.2 data and the explicit
relative ideal required by 7.26. `downstream-kernel-and-preservation-draft.tex`
is a mathematical draft for the receiving sessions to verify and assemble.
It is not a completed native Section 7 or Section 8 result. Discoverable
notes also live at `../../section 7/SECTION6-HANDOFF.md` and
`../../section 8/SECTION6-HANDOFF.md`.

## Review

`review/section6-aperture-revision-applied.pdf` contains eight actual
manuscript pages with the applied changes in orange. All eight were
rendered and visually inspected. The canonical manuscript compiled;
font-cache workarounds were confined to the scratch review copy.
The right-panel display request returned queued.
The exact aperture-only patch is `applied-aperture-revision.patch`.
