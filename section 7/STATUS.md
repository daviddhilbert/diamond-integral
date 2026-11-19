# Section 7 status

Updated 2026-11-19. Audit: `lake env python3 'section 7/verify.py'`
(receipt `verification/status.json`; complete public types and transitive
axioms; only `propext`, `Classical.choice`, `Quot.sound`).

## Manuscript

The §7 main text is already revised for bounded variable apertures and J_var
(R118–R137, R171 resolved). No further manuscript change has been made in this
session. Notes found while formalizing are in [GAP-REPAIRS.md](GAP-REPAIRS.md);
none is a mathematical error.

## Complete numbered results

Lemma 7.5, Corollary 7.6, Lemma 7.7, Corollary 7.8, Definition 7.9, and the
additive part of Lemma 7.10, together with Definition 7.2 on isomorphism classes.
See [COVERAGE.md](COVERAGE.md) for the declaration map. They hold over an
arbitrary parameter base and take no input beyond the ACVF model.

## Supporting native proofs

- `BoundedClasses`: isomorphism classes of μRV^db[k] form a commutative monoid
  under the tagged disjoint union. The coproduct laws are actual measured
  isomorphisms. The module also gives restriction and gluing along definable
  pieces, the map to Section 4's ring K μRV^db[*], and the refinement property.
- `RVMaps`: original-base definability of maps built from coordinates, graphs and
  RV multiplication or division, and of `vrv g < vrv h` and `vrv g ≤ vrv h`.
- `ElementaryComparison`: the four explicit comparison isomorphisms of 7.5.

## M3 progress (lift side)

- `StrictCharts`: every bounded chart is isomorphic to an `∞`-free chart. The
  labels are encoded with the tags 1 and rv(−1), which residue characteristic
  zero separates.
- `LiftClasses`: `rvCls : Cls → K₊ μRV^db[k]` (Section 6's
  `rvPresentation`) is additive, and `liftCls : Cls →+ K₊ μVF^◇[k]` composes it
  with Section 6's `liftHom`.
- 7.12 is in progress, following the pipeline in PLAN.md. The Section 6 tools
  are:
  - `RelativeApertureData` and `DiamondSpecialIsomorphisms.remark_6_15` (a
    chain gives a morphism);
  - `lemma_6_30_tuple_vfGenerated` with `TupleFinitaryLift.continuousAt`
    (focus b₀ and endpoint b₁);
  - `rvFamilyMap` (Maps from definable label families);
  - `gammaFibreValue`/`gammaFibreValue_named` and
    `gamma_value_named_on_rv_fibre` (named radii);
  - `RVGrafting.graft` with `graft_properHomeomorphism`;
  - `contractedMeasuredRVObject`;
  - `lift_isomorphic_pos`.
- Still to do in M3: surjectivity of `liftCls` (needs a converter from
  `MeasuredRVObject` back to charts), 7.11, and 7.13.

## Next

Product compatibility (7.10), Remark 7.4's named bound, and the object-level
converse for Definition 7.2. Then milestone M3 (7.11–7.13; the lift to μVF^◇,
including ∞-free conversion of labels), followed by M4/M5 and M6 as in PLAN.md.
