# Section 7 session: proposed manuscript revisions

These batches use the format of `Section7/make-review.py`: `EDITS`, `RESOLUTIONS`, `ANCHORS` and `TITLE`. They are built here by `build-review.py`, which reads this repository's manuscript and writes the review extract into the batch folder.

## B11: Definition 6.24, relatively unary in a single coordinate (2026-11-20)

**Status:** applied to the manuscript on 2026-11-20 on the author's decision to go back to the single-coordinate definition in the paper and in Lean (`B11-relatively-unary-single-coordinate/approval.json`; review extract: `B11-relatively-unary-single-coordinate/section7-B11-relatively-unary-single-coordinate-review.pdf`). The author decided the change from a description of the edit; the wording of the extract was not separately reviewed before it was applied.

**The edit.**
- Definition 6.24: a definable bijection G : A → B is relatively unary in the i-th coordinate if pr_ĩ ∘ G = pr_ĩ. The same for morphisms of RV[k]. The pair (i, j) is gone.
- The sentence "Alternatively, for simplicity, we may take i = j in this definition and stipulate that the condition in question holds up to coordinate permutations" is removed.
- In the description of the transformations T_i before Definition 6.26, "relatively unary in the (i, i)-coordinate (up to coordinate permutations)" becomes "relatively unary in the i-th coordinate".
- The gluing sentence ("Since identity functions are relatively unary in any coordinate, …") is unchanged; it is now correct as written.

**Why.** With the pair (i, j), the identity is relatively unary only for i = j, so the gluing sentence did not cover steps with i ≠ j. The single-coordinate form is Definition 5.4 of "Integration in algebraically closed valued fields". Outside the definition the manuscript names no pair with i ≠ j, and every step constructed in the formalization keeps all VF-coordinates other than one.

**Lean.** Section 6 `UnaryFactorization.step`, `IsStep.unary`: `n = 0 ∨ ∃ i, VFUnaryRelativeAt f i`; see the Section 6 GAP-REPAIRS entry under Definition 6.24 and Section 7 GAP-REPAIRS 19.

**Not in this batch.** The gluing sentence leaves one detail implicit: the intermediate images of different pieces must stay disjoint (an additional RV-coordinate does it). No text was proposed for this.

## B10: Definition 6.34, compositions inside μVF^◇ (2026-11-20)

**Status:** approved by the author and applied to the manuscript on 2026-11-20 (`B10-diamond-intermediate-objects/approval.json`; review extract: `B10-diamond-intermediate-objects/section7-B10-diamond-intermediate-objects-review.pdf`). Before approval of the last sentence, the author asked to have it checked against the paper; it was replaced as described next, and the author then gave the instruction to apply the batch.

**The checked sentence.** The first draft justified the transported forms by the covariance of the fibers of the inverse map and a uniform bound from Lemma 2.41 (`db:to:db`). That does not match the paper: a volume form is proper covariant when each of its fibers A_γ is proper invariant (the definition of a proper invariant pair (A, ω) in Section 6), which asks for no uniform radius, and covariance of a fiber for one pair of radii does not give the radius needed by ω. The sentence now uses the paper's own lemmas: T_i ∘ ⋯ ∘ T_1 is a proper covariant homeomorphism (Lemma 6.14, `spec:inve`), so its restriction to the proper invariant subset A_γ is one too and the image of A_γ is proper invariant (Lemma 6.8, `conv:unif`, third and first claims).

**The edit.**
- Definition 6.34 states explicitly that the composition is taken inside μVF^◇[k]. Every intermediate object is proper invariant, with its own proper covariant volume form, and every factor is Γ-measure-preserving on its own.
- Remark 6.35 records three things:
  - composites and inverses stay inside μVF^◇[k];
  - special covariant bijections are morphisms with the transported forms, and the lifts of Lemma 6.33 pass through lifts of RV objects;
  - a counterexample shows the intermediate objects are needed: F(x, z) = (x, x·κ(z/x)) on 𝒪².

**Why.** The proof of Proposition 7.24 applies Corollary 7.15 to each factor ("a sequence of relatively unary μVF^◇[k]-morphisms, which exists by definition"). Corollary 7.15 compares standard contractions of both ends of a factor, so both ends must be objects.

**Lean.** Section 6 `DiamondCategory.ObjectFactorization` and `IsStep`; see the Section 6 GAP-REPAIRS entry under Definition 6.34 and Section 7 GAP-REPAIRS 16.

The route was approved by the author (fix (1)).
