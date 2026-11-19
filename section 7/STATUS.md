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

## Next

Product compatibility (7.10), Remark 7.4's named bound, and the object-level
converse for Definition 7.2. Then milestone M3 (7.11–7.13; the lift to μVF^◇,
including ∞-free conversion of labels), followed by M4/M5 and M6 as in PLAN.md.
