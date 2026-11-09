# Lean formalization plan

**Forey and Yin, _Bounded integral and motivic Milnor fiber_**

The working source is `diamond_integral_revision_annotated.tex`, with
`diamond_integral_revision_annotated.pdf` for printed numbering and pagination.
Use LaTeX labels as stable identifiers across revisions. Record the manuscript
version, printed number, and relevant purple referee or blue author notes when
opening a target. Keep the annotated source as the reference for proposed
corrections.

## Layout and order

Section 1 is the introduction. Record its technical claims in the sections
where they are defined and proved.

| Folder | Annotated PDF | First work and exit milestone |
| --- | --- | --- |
| [Section2](Section2/README.md) | pp. 10–24 | VF/RV/Gamma/DC conventions, parameter bases, discs, atoms, continuity and fiberwise results. Start with §2.1 and Lemma 2.11. |
| [Section3](Section3/README.md) | pp. 25–28 | Grothendieck constructions and VF, RV, RES and Gamma categories with and without volume forms. Establish lifting and the two HK integral presentations at their stated parameter scope. |
| [Section4](Section4/README.md) | pp. 29–35 | Prove the unmeasured and measured retractions to their respective RES targets. Verify Euler characteristics, convolution, interval generators and factorization through each quotient. |
| [Section5](Section5/README.md) | pp. 36–46 | Prove the reduced-section and twistoid lemmas, then tropical Fubini and the fiberwise equality theorem. Track witness uniformization and arithmetic residue descent separately. |
| [Section6](Section6/README.md) | pp. 47–61 | Prove proper covariance and standard contraction results, then lifting into the proper invariant categories. Audit Jacobians, global bounds, continuity and finite RV fibers under the actual operations. |
| [Section7](Section7/README.md) | pp. 62–70 | Check the unary annular blowup relation, prove the 2-cell and contraction-order comparison, then identify the bounded lift kernel and construct the bounded integral (Theorem 7.26). |
| [Section8](Section8/README.md) | pp. 71–80 | Prove the equivariant fixed-order coefficient comparison, rationality and the limit identity for motivic Milnor fiber (Theorem 8.11). Track the extended bounded zeta construction separately. |

Read and specify targets in paper order. For a forward dependency, identify
the exact statement and schedule the smallest prerequisite first. Record the
dependency and resume the section after its proof. In particular, §5 cites
preparation whose bounded counterpart is developed in §6. Its unbounded
polynomial preparation target can be compared directly with Yin's
*Special Transformations*, Theorem 5.5.

## Reuse and compatibility

- Use the existing two-sorted ACVF language. The neighboring *Special
  Transformations* checkout pins
  [ACVF-QE](https://github.com/daviddhilbert/ACVF-QE) at
  `f3ef4ee679f921079aa8f742a2807a9cc724d2d6`, Lean `v4.33.1`, and
  Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Start the compatibility
  check with this combination. Pin the versions used after checking the actual
  target repo and the integration development.
- In [*Special Transformations*](https://github.com/daviddhilbert/special-transformations),
  inspect the section libraries and their verification records. Start with
  `Section3.BallGeometry`, `Section3.GeneralBallCenters`, `Section3.VFAlgebraicity`
  and `Section3.GammaBaseCMinimal`. Sections 4–7 supply candidates for
  categories, dimension, special bijections, henselian descent and lifting.
  Sections 9–10 supply Jacobian and measured-lifting candidates. Published
  checkpoints, local repairs and explicit hypotheses have separate status.
- Locate the Lean checkout for Yin's [*Integration in Algebraically Closed
  Valued Fields*](https://arxiv.org/abs/0809.0473). Map its checked exports
  for HK kernels, elementary blowups and contraction comparisons to §§3 and 7.
  Compare the proper-invariance and boundedness requirements before applying
  an unbounded theorem. The checkout and reusable revisions are to be confirmed.
- Compare definitions before importing each headline. Preserve equicharacteristic
  zero, the actual parameter base and saturation requirements, the single
  RV zero/infinity element, the reversed valuation order in the existing Lean
  encoding, and the distinction between an RV class and a value-group fiber.
  In particular, distinguish VF-generated, (VF,Gamma)-generated, arbitrary
  RV-parameter, and disc-imaginary bases. Track descent back to the original base.

## First proof session

1. Inspect the target repository and check that the QE package and selected
   Special Transformations modules build at a compatible revision.
2. In §2.1, map the manuscript's coordinate, ball and RV-fiber conventions onto
   the existing types. Check R022–R024. Include the singleton zero RV fiber,
   preserve existing RV tags under the hull, and use uniform open/closed disc
   codes. Check the R023 counterexample and inventory later uses of continuity
   before deciding whether to use a stronger topology or add local hypotheses.
3. Open Lemma 2.11 (`cut:to:hensel:substru`). Its base is VF-generated with
   nontrivial value group. Compare the existing henselization and definable
   closure statements in Yin's §6. Check both directions and closure in the
   RV sort over the same base. Record any explicit valued-field input with
   its exact statement and status.
4. Continue with Lemmas 2.12–2.14. Look for finite-set internalization and
   singleton exchange at the required scope, and compare Lemma 2.13 with
   the checked VF-algebraicity result from Special Transformations §3.

## How a lemma moves from manuscript to Lean

For each numbered target, record its LaTeX label, exact statement and
parameter base, dependencies, Lean declaration, referee IDs and proof status.
Group tightly related declarations into one module. Expose verified results
through a section entry point as sections acquire proof code.

Check each referee claim against the statement, the proof and its callers.
For a false claim, preserve a counterexample and propose a precise replacement.
For a proof gap, record the missing implication and attempt it under the stated
hypotheses. For a change of mathematical scope, keep the original statement
and the proposed correction in the record for author review. Apply accepted
corrections to the manuscript and Lean together.

A completed target has a passing build in the pinned environment, a checked
full theorem type, and a `#print axioms` audit of the actual export. Use the
existing project's standard allowance of `propext`, `Classical.choice` and
`Quot.sound`. Audit explicit premises separately and identify conditional
results as such. When correcting an earlier statement, recheck affected
exports in downstream sections.

## Specific obligations to track

- **§2, R023 and R040–R046.** Test the continuity convention under composition
  and verify the exact parameter and lifting conditions for curve selection,
  compactified graph arguments and the downstream openness claims.
- **§3–4, R053, R060 and R062–R071.** Put the generation hypothesis on the
  lifting map, distinguish measured and unmeasured quotient targets, and
  verify the domain and vanishing of each ideal generator.
- **§5, R088–R089 and R095.** Prove the Fubini statement first in the original
  definable RES target. For arithmetic realization, retain residue-field descent
  together with inertia and require the ramified quadratic counterexample as
  a test of any proposed restriction to unramified points. For VF-to-RV
  descent, check uniformization of the complete finite congruence witnesses.
- **§6–7, R102, R170 and R134–R136.** Check the locus where Jacobian equations
  hold under composition and whether an RV-hull preserves finite RV fibers.
  Prove the contraction-order comparison and parameter descent before
  deriving the global bounded kernel.
- **§8, R144, R146, R148 and R173.** Check the equivariant affine-action quotient,
  work first with the finite lattice trace at fixed order, and prove normalized
  class invariance under compatible truncation cutoffs. Test the shear in
  R173 before choosing a cutoff lemma. Give rationality, the limit map, and
  any extension beyond doubly bounded support their exact domains.
