# Corrected upstream pins: Sections 2–6 compatibility

The November 16 migration adopts Special transformations v1.1 at
`25852c85a31c67069b148bd31348128318303510` and Integration in ACVF main at
`7675d31332f20421c803ea16af84964ed74cd51f`. The latter packages proof commit
`862aa448b4314df673bccd928d1353af6650d7f1`; the section proof files are unchanged
between those revisions. Lean, Mathlib and ACVF-QE revisions are unchanged.

Upstream verification is retained in `special-v1.1.json`,
`integration-checkpoint2041.json`, and `integration-project-integrity.json`.
The earlier Integration checkpoint correctly records remote CI as pending;
the later integrity report records its passing proof CI run
[43851204054](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43851204054).
The run and every verification step were also checked directly through GitHub;
`integration-ci-jobs.json` retains that response. This is evidence for the
published proof commit, not a claim that a later
packaging commit has separately passed the same CI run.

All 30 Special transformations open-radius corrections are now published
byte-for-byte. Integration publishes its nine radius consumers, with additional
proof-body simplifications, and all 250 completed Section 5 overlay files.
Preparation verifies these published hashes instead of applying the historical
radius patches. Only the two existing Section 6 hypothesis-scope adapters remain
local. Their premises and the actual `completed_section5_input` producer are
retained. Preparation preserves unexpected edits and has a read-only check mode.

Run the five section verifiers, then
`lake env python3 verification/verify-upstream-weighted-zero.py`.
`status.json` is produced only after the new-pin receipts, proof-source hashes,
exact dependency layers and complete measured-interface type/axiom audit pass.
The source-hash-identified historical aperture receipts retain their original
pins; the current section receipts and this migration receipt supersede them
for dependency compatibility.

The local Gamma-valued categories already retain arbitrary finite definable
weighted zero objects. The audit checks the actual zero lift and its full/faithful
comparison, both forms in mixed products, finite Gamma tensor absorption,
weighted RES coefficient embeddings, the relative-annular quotient's degree-zero
injection and measured aperture comparison, and the exact zero-arity 6.31 identity.
The corrected Special transformations Gamma-zero exports are checked at their
full types alongside those local interfaces. This is a compatibility check, not
an assertion that all the different presentations are definitionally equal.

Four Section 3 records remain the same precise accepted cited inputs:
`YinMeasuredLiftInput`, `YinDegreeMeasuredLiftInput`,
`YinGammaGroundMeasuredLiftInput`, and `YinGammaGroundDegreeMeasuredLiftInput`.
They require Gamma-valued lifting, surjectivity and exact kernels. The new
Integration Section 7 HK theorem is about nonzero RV-valued forms. Names referring
to a Gamma parameter base do not change that density codomain. Neither its name
nor valuation of an existing RV form supplies a same-base RV lift of every Gamma
form. No general definable Gamma-to-RV section is assumed. The new upstream
kernel therefore does not silently discharge these four records. Their
conditional consequences retain exactly that status.

This migration changes no local mathematical proof body or manuscript statement.
It preserves revised 6.11 and 6.38, and the constant-aperture witnesses for full
6.19. It does not prove the independent bounded-aperture kernel in this paper's
7.26, equate the old scalar ideal with the relative ideal, or complete Section 8.
