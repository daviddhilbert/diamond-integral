# Cross-section dependency audit

This audit distinguishes checked upstream reuse from results proved relative
to explicit author-accepted inputs. It does not change any mathematical
statement or add an assumption. The machine-readable record is
[section-boundaries.json](verification/section-boundaries.json).

| Consumer | Checked connection | Remaining boundary |
| --- | --- | --- |
| Section 2 | All eight numbered geometric interfaces from [18, §3] have compiled constructors, including original-base and finite-disc-name transport. The complete Section 2 audit passes: 850 public theorems and 378 reuse declarations. | General piecewise rational-affine Γ background remains an accepted explicit input. The unconditional legacy interfaces are not substituted for the scoped constructors. |
| Section 3 | Compiled Section 2 imports and the eight [18, §3] constructors are included in its full audit. Both corrected tensor kernel presentations are proved locally. Its 1,004 Lean source files match the passing receipt. | Later [18] lift/kernel records remain explicit. Available unmeasured §6 exports still require closure/category transport and carry the unfinished §5.8 input. Measured §7 is unavailable at the pinned revision. The approved Reichstein–Youssin consequence remains explicit. |
| Section 4 | Statements and hypotheses agree with finalized Section 3 at `37c8361`. The complete categorical-to-chart factor/tensor/target equivalences, scalar and comparison squares, and elementary-pair ideal transport are compiled. `Section3T001Integration` constructs both interfaces; linked Propositions 4.7 and 4.15 take no T001 input. No manuscript correction is required. | General rational-affine Γ background remains explicit; already accepted external Section 3 citations retain their documented scope. |
| Sections 5–8 | Each directory currently contains a planning README. | No local Lean implementation or completion certificate exists to audit yet. Their dependency boundaries must be checked as they are implemented. |

Section 1 is introductory and has no local Lean section library.

The Section 2 constructors are in Section 3 to avoid a cyclic import. They
instantiate the original interfaces; their presence does not erase the
hypotheses from the scoped final wrappers. In particular, ball atomicity
and disc partitions retain genuine saturation at an infinite cardinal.
The 2.30 wrappers additionally retain the stated small real base, and all
wrappers retain ACVF(0,0) and nontrivial definable Γ where required. Finite
real support preserves the original imaginary names. No chosen ball centre
or RV representative is added to the ground base.

The later [18] source uses a definably closed generated base. The local
`GammaGroundContext` separately records language generation of the real
substructure and its Γ subgroup. These contexts have not been silently
identified. An exact imported export is consequently distinguished from a
constructor of the local legacy lift record. Measured lift/kernel inputs
are retained because the upstream measured formalization is absent.

The legacy `YinGammaAffineInput` helper also remains explicit in its own
conditional wrappers; those helper names are not evidence that the newer
full-ground classification or tensor results assume that interface.

A focused Lean audit prints 32 actual boundary declaration types and their
logical dependencies in
[SectionBoundaryAudit.lean](verification/SectionBoundaryAudit.lean), with
[the complete output](verification/section-boundary-types.txt). It passes
with only `propext`, `Classical.choice` and `Quot.sound`. This logical-axiom
check is separate from the explicit mathematical inputs listed above.
No HK result is an accepted input. The later [18] inputs and R–Y input are
within the author's existing authorization.

Sources: [Section 2 upstream links](section%202/verification/UPSTREAM-LINKS.md),
[Section 3 reuse inventory](section%203/verification/integration-reuse.json),
[Section 3 paper coverage](section%203/verification/paper-targets.json), and
[Section 4 statement audit](section%204/verification/final-section3-audit.json).
The dependency pin is `7d4acc730496b3bd05a22c268ffd89540ca694f9`, with
the recorded compatibility patches; no new revision is substituted by this
audit. The author subsequently authorized committing and pushing the completed work.

Recheck the focused types and local proof-source receipts with
`python3 verification/audit-section-boundaries.py` after activating the
project Lean environment. Full section checks remain their own `verify.py`
scripts. The final Section 4 audit covers 600 modules, 4,998 declarations
and 3,027 theorems.
