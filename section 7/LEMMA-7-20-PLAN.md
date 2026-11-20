# Lemma 7.20 (`decom:into:2:units`): proof plan

Target: a theorem with exactly the type `TwoCellInput.Lemma720 M G` (input committed in 83afb3ac),
in modules `section 7/Lemma720*.lean`, registered in the `[[lean_lib]]` block
"section 7 lemma 7.20" at the end of `lakefile.toml`. No `sorry`, no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`. No Hrushovski–Kazhdan input.

## Mathematical route

Notation: `A ⊆ VF² × RVʳ` proper invariant over `T`. Order `e = 1`; the first stage contracts
coordinate 1 (`y`), the second contracts coordinate 0 (`x`).

1. **Normalization.** `N : ZeroCenteredData A` (`exists_zeroCentered_data`). `B₀ := N.map.image`
   (reindexed by `e = 1`), proper invariant and doubly bounded.
2. **Stage 1** (`exists_shear_contraction_stage_all_dimensions`). Its displacement is
   label-determined, so it has a definable, continuous offset `ε₀(x, w)` on the contracted set
   `B₁ ⊆ VF × RV^{a₁}` (`graphShearBaseDisplacement`). Fibre lemma: over `(x, w) ∈ B₁`, the
   `y`-fibre of `B₀` is `ε₀(x, w) + t(w)^♯`, with `t(w)` the leading label.
3. **Data on `B₁`**, as RV relations, uniformly in the labels `w`:
   - the locally-constant locus `L` and finite codes `e₀` on it; injectivity codes `e₁` off `L`
     (upstream `FamilyPositionRefinement.constant_or_injective`, a scalar-family statement over
     a full base without VF generation);
   - the RV-slope rows `SlopeAt(x, vrv b, t)` (radius encoded by an RV element);
   - membership in the pieces of a disc-to-disc partition of the bijection
     `(x, w) ↦ (ε₀(x, w), w ⌢ e₁(x, w))` off `L` (`Section3.integration_lemma_2_32`).
4. **Obstacles.** `exists_unary_obstacles` gives one finite `T`-definable `Q ⊆ VF` such that all
   these rows are constant on every open disc avoiding `Q`.
5. **Protected neighbourhood of `Q`.** For `z ∈ Q` and labels `w` with `z ∈ B₁_w`, let `θ(z, w)` be
   the least radius on which `x ↦ ε₀(x, w) + t(w)^♯` is constant around `z` (continuity of `ε₀`).
   `U := {(x, w) ∈ B₁ : ∃ z ∈ Q, v(x − z) > r(z, w)}`, where `r` is at least `θ`, the invariance
   radius of `B₁_w` and the pairwise distances in `Q`. `U` and `B₁ ∖ U` are proper invariant.
6. **Stage 2.** `unary_proper_preparation` on `B₁` with the pieces `U` and `B₁ ∖ U`, then
   regularization: a chain-backed unary stage. Its fibres are translates `c + t'^♯` of RV-discs
   (`unary_rv_displacement`), each inside `U` or disjoint from it.
7. **Assembly.** Program = stage 1, then stage 2, then `.zero`; lift from
   `exists_ordered_standard_contraction_lift`. Then
   `cellAt F s = {(x, y) : x ∈ D_s, y ∈ ε₀(x, w(s)) + t(s)^♯}`.
8. **Fibre analysis.**
   - `D_s ⊆ U`: `D_s` lies in one ball around a unique `z ∈ Q`, the fibres are constant, and
     `ε := ε₀(z, w)` is constant (kind 0).
   - `D_s ∩ U = ∅`: `D_s` avoids `Q`, so all rows are constant on it.
     - Inside `L`: `ε₀` is constant (codes `e₀`), kind 0.
     - Off `L`: `ε₀` is injective (codes `e₁`), rv-affine (constant slope rows and
       `RVLinearRadiusClosure.on_ordinary_ball`) and disc-to-disc (one partition piece). The cell
       is kind 1 if `rad ε₀(D_s) ≥ vrv t`, else balanced (kind 2) with `t₁ = −t/slope`.
9. **Uniform data.** `ε(s, ·)`, `t(s)`, `t₁(s)`, `kind(s)` are defined by cases that are
   definable over `T`.

## Status

See the commit log on `claude/lemma-7-20-5dfcd3`.
