# Cross-section dependency audit

This audit separates checked upstream reuse from results proved relative to
explicit author-accepted inputs. It does not change any mathematical statement
or add an assumption. The machine-readable record is
[section-boundaries.json](verification/section-boundaries.json).

Updated November 18, 2026, after the second numbered-coverage audit of
Sections 2–6 and the repairs recorded in each section's `GAP-REPAIRS.md`.

| Consumer | Checked connection | Remaining boundary |
| --- | --- | --- |
| Section 2 | All eight numbered geometric interfaces from [18, §3] have compiled constructors in Section 3. Discharged wrappers now cover every Section 2 headline that took them: 2.23, 2.25 (open/closed), 2.27, 2.28, 2.30 and 2.32 as before, plus 20 more statements in `section 3/Section2CitedInputsDischarged.lean` (2.23–2.26, 2.29 and 2.35 variants with disc names). The unary Γ rational-affine input is proved (`Section5.GammaQE.gamma_piecewise_rational_affine`). Discharged 2.41, 2.47 and 2.53 are in `section 3/Section2GammaLinearityDischarged.lean`. The full Section 2 audit passes: 970 public theorems and 378 reuse declarations. | The originals keep their input parameters; the discharged forms are separate declarations. Where the original stated no saturation, the atomicity constructor supplies it, which is a standing hypothesis. Remaining items are recorded as "Not pursued" in the triage. |
| Section 3 | Compiled Section 2 imports and the eight [18, §3] constructors are in its full audit. Both corrected tensor kernel presentations are proved locally. The [18] lift/kernel records are produced locally from completed [18] proofs (`completed18GroundLiftInput`, `completedGammaGroundBoundedLiftInput` and the four `completed*MeasuredLiftInput` records). The §5.8 two-order input is discharged (`completed_section5_input`). Theorem 3.22's measured integral is a graded isomorphism (`theorem_3_22_measured_graded`). The full audit passes: 3,895 theorem types over 1,528 Lean files. | The Reichstein–Youssin consequence (`ReichsteinYoussinInput`) remains the explicit, author-approved input of Remark 3.15 and the 3.18 witness. The [18] §5/§6 proofs are used through the overlay in `section 5/dependency-overlay` and `section 3/reuse/integration-open-radius.patch`, not the pinned package verbatim. |
| Section 4 | Statements agree with finalized Section 3. `Section3T001Integration` constructs both T001 interfaces. Propositions 4.7 and 4.15 take no T001 input. Discharged versions without the Γ-linearity input are in `Section4GammaLinearityDischarged.lean`. Diagram (edb:eb:com) and Remarks 4.4/4.16 are linked in `Section4LinkedRemarks.lean`. Lean's μRV^db, which allows ∞ coordinates, is proved isomorphic to the paper's ∞-free ring (`RVStrictBoundedComparison.equivalence`). The full audit passes: 5,493 declarations (3,340 theorems) over 622 Lean files. | Remark 4.2's continuous cell decomposition needs the multivariate rational-affine normal form (`Section3GammaAffineInput`). Section 5 discharges only the unary form. |
| Section 5 | The requested scope (Lemma 5.12 onward) is formalized with every input discharged and no HK result: both Fubini theorems, including RV[*] fibres (`WeakDegreeFubiniDischarged.lean`); the inflated-family Fubini theorem and its Vol version (`InflatedFamilyFubini*.lean`); the actual-variety corollary. The ambient model these take is constructed in ZFC (`PuiseuxMonsterAmbient.lean`). The ambient Θ is a ring isomorphism (`ambientPuiseuxComparisonEquiv`). The full audit passes. | Author-approved omissions: the cross-section expansion and the [19] computations; Remark 5.16, Remark 5.18's examples and the global twist:C formula ("Not pursued"). |
| Section 6 | All numbered results are formalized in the recorded context, including Remark 6.20 in every VF-dimension (`Remark620.lean`, through the `Row*` row-form mirror). Lemma 6.38 has rv-contractible forms and a μRV^db[1] morphism. Remark 6.35 is a groupoid. Lemma 6.29 holds in all degrees. 43 numbered statements have discharged versions without the Γ-linearity input. The full audit passes: 5,811 declarations over 1,453 Lean files. | Remark 6.17 and the multi-dimensional extension of Lemma 6.16 were dropped by author decision (the unary 6.16 is formalized). Example 6.25 and the remarks listed as "Not pursued" in the triage are not formalized. |
| Section 7 | Five modules build the μVF^◇ material requested from Section 6's Definitions 6.34–6.37 (`ChartLifting`, `ChartDiamondLift`, `MeasuredRVBounds`, `MeasuredRVBridge`). | The Section 7 kernel and specialization assembly are deferred. |
| Section 8 | Planning README and handoff only. | No local Lean implementation yet. |

Section 1 is introductory and has no local Lean section library.

The Section 2 constructors are in Section 3 to avoid a cyclic import. They
instantiate the original interfaces, and their presence does not erase the
hypotheses of the scoped final wrappers. In particular, ball atomicity and
disc partitions keep genuine saturation at an infinite cardinal. The 2.30
wrappers also keep the stated small real base, and all wrappers keep
ACVF(0,0) and nontrivial definable Γ where required. Finite real support
preserves the original imaginary names. No chosen ball centre or RV
representative is added to the ground base.

The later [18] source uses a definably closed generated base. The local
`GammaGroundContext` separately records language generation of the real
substructure and its Γ subgroup. These contexts have not been silently
identified. Section 5 now constructs a `GammaGroundContext` for the Puiseux
ambient (`exists_puiseux_ambient`), so statements over this context are not
vacuous.

The legacy `YinGammaAffineInput` helper remains explicit in its own
conditional wrappers. Those helper names are not evidence that the newer
full-ground classification or tensor results assume that interface.

A focused Lean audit prints the boundary declaration types and their logical
dependencies in [SectionBoundaryAudit.lean](verification/SectionBoundaryAudit.lean),
with [the complete output](verification/section-boundary-types.txt). It uses
only `propext`, `Classical.choice` and `Quot.sound`. This logical-axiom check is
separate from the explicit mathematical inputs listed above. No HK result is
an accepted input. The R–Y input is within the author's existing
authorization.

Sources: [Section 2 upstream links](section%202/verification/UPSTREAM-LINKS.md),
[Section 3 reuse inventory](section%203/verification/integration-reuse.json),
[Section 3 paper coverage](section%203/verification/paper-targets.json),
[Section 4 statement audit](section%204/verification/final-section3-audit.json),
and the `GAP-REPAIRS.md` file of each section.

Dependency pins (`lake-manifest.json`, after integrating `origin/main`
a6a77c4 on November 18, 2026): `fubini_theorems` at
`05587564f70fd0015fbb7b7dbf4a8d8c4b0b64f5`, `integration_in_acvf` at
`ab4c0e8b15e1e21b0b4fce57eed764be76020e06`, `hilbert-mathlib` at
`88bb3386f616779bfd87eb453d8a7c899ad63961`, `special_transformations` at
`423c767a84b709487da7e798f70f0639545db1ac`, `acvf_qe` at
`173708265d7959e031bf9552ee884501fc21f2cb` and Mathlib at
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The `acvf_qe` manifest entry was
aligned with the lakefile and verifier pin; a6a77c4 had left it at
`a4138c3`, which made that commit's CI fail. Shared foundations and the
Section 5 bodies come through the byte-checked compatibility imports listed in
`verification/EXTRACTED-FOUNDATIONS.json`.

The sixteen Section 5 modules added on November 18 (the `Inflated*` files,
`WeakDegreeFubiniDischarged`, `PuiseuxMonsterAmbient`,
`ElementaryRESExtension(Data)`, `Lemma519Polynomial` and `Test520Tuples`) are
still compiled here as real modules, not compatibility imports, until they
are moved into Fubini-theorems.

Recheck the focused types and local proof-source receipts with
`python3 verification/audit-section-boundaries.py` after activating the
project Lean environment. Full section checks remain each section's own
`verify.py`.
