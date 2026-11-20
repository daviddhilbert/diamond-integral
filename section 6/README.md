# Section 6 — Special covariant bijections

Definition 6.11 and Lemma 6.38 now use the bounded variable-aperture class.
`RelativeApertureData` includes actual focus and endpoint graphs, endpoint
continuity on fixed-label fibres, the exact leading-term identity, and a
named finite bound on the nonnegative relative valuation. Its maps have
proved inverses, full core images, double bounds, proper covariance and
the approved almost-everywhere unit total Jacobian in every VF arity.
`RelativeApertureChain` supplies the finite compositions.

`ScalarApertureInclusion` identifies the original scalar point maps with
members of the new class. Existing preparation and contraction proofs,
including full 6.19, remain valid constant-aperture witnesses.
`UnaryApertureInclusion` embeds the constructed unary chains in the same
precise arbitrary-arity class. `BoundedVariableUnaryMatching` proves revised
6.38 from the original proper objects and actual forms: both preparations,
the literal conjugate, the actual RV bijection and the volume identity at
every retained label. The original base remains VF-generated; retained RV
fibres need not be finite in this matching theorem.

The earlier numbered results remain exported by `Section.lean`: 6.5–6.9,
approved AE 6.14, 6.16, full 6.19 and 6.21, 6.22–6.23, standard contractions
6.27 with normalization and all coordinate orders, all four 6.29 variants,
unary 6.30, measured and unmeasured 6.31 in every degree, and measured
relatively unary chain lifting 6.33. Precise model, saturation, smallness,
Gamma-affine background, original-base and volume-form hypotheses are
explicit in their public types.

November 17–18 additions (see [GAP-REPAIRS.md](GAP-REPAIRS.md); latest audit
PASS, 5811 declarations):
- the category μVF^◇ of Definition 6.34 (`DiamondCategory.lean`), Remark 6.35
  (isomorphism is an equivalence; `DiamondGroupoidMaps.lean` gives a
  `CategoryTheory.Groupoid` instance whose morphisms are the underlying maps)
  and Corollary 6.37 (`liftHom_surjective`, every degree k ≥ 0);
- Lemma 6.29 in every degree including 0, all four variants
  (`lemma_6_29_all_degrees`, `lemma_6_29_measured_all_degrees`,
  `lemma_6_29_doublyBounded_all_degrees`,
  `lemma_6_29_measured_doublyBounded_all_degrees`), and `lemma_6_33_diamond`
  in every degree;
- Lemma 6.38: `lemma_6_38_diamond`, and the contractible versions
  `lemma_6_38_bounded_variable_apertures_contractible` (with finite RV
  fibres) and `lemma_6_38_diamond_contractible` (no extra hypothesis);
- Remark 6.20 in every VF-dimension (`Remark620.lean`: `remark_6_20`), with
  the measured preparation mirrored for row forms in the `Row*.lean` modules
  (`RowForms.lean`); the unary case is `remark_6_20_unary`;
- Remarks 6.4, 6.12, 6.15, 6.28, 6.32, Definitions 6.11 (contracted layer)
  and 6.24, and tuple 6.30;
- `Section6GammaLinearityDischarged.lean`: 43 `_discharged` statements without
  the Γ rational-affine input, which is now proved
  (`Section5.GammaQE.gamma_piecewise_rational_affine`); the original
  statements still take it as a parameter.
Lemma 6.16 (A is a literal subset of VF, hence unary) is formalized as
`lemma_6_16` (`UnaryPreparation.lean`); only the multi-dimensional extension
(Remark 6.17, every definable A) was dropped by author decision.
The author-approved "not pursued" items are listed in GAP-REPAIRS.md. The
closing docstring of `Section.lean` predates these additions.

Pure RV variable-aperture compatibility is owned by `section 4`; the five
similarly named files here are imports retained for compatibility. The
approved completed Section 5 snapshot and dependency overlays are the
upstream baseline for the integrated verification. No Section 5 session
source has been modified.

Run `python3 'section 6/verify.py'` from the worktree, with the pinned
Lean 4.35.0 toolchain on PATH. It builds the entry point and checks every
public declaration's complete type and transitive axioms. The allowed
logical principles are `propext`, `Classical.choice` and `Quot.sound`.
The fresh receipt records the exact source hashes and package pins.

Section 7 must apply the corresponding 7.2 change and prove its revised
kernel theorem for the explicit relative ideal. Section 8 must check its
geometric specialization. Those tasks are deferred to their own sessions;
proof support here does not certify their completed assemblies. See `reference/REVIEW.md`, `reference/downstream-handoff.txt`, and the
Section 7–8 `SECTION6-HANDOFF.md` notes.
The earlier chronological record is retained in
`verification/history/section6-README-before-aperture-adoption.md`.
The author authorized committing and pushing this Section 6 revision, its
necessary upstream changes and the Section 7–8 handoff notes on November 15.

The November 16 corrected upstream migration is documented in
`verification/upstream-weighted-zero-upgrade/README.md` at the repository root.
Current Sections 2–6 receipts record the new pins. It preserves all local
Section 6 proof bodies, including the exact zero-degree form identity. The
four Section 3 Gamma-valued lift/kernel records it mentioned as retained inputs
have had proved producers since November 17
(`section 3/verification/GAMMA-KERNEL-COMPLETION.md`); they are not accepted
cited inputs.
