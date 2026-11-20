import «section 7».SliceContractions
import «section 7».FibreGood2

/-! Lemma 7.23 (`contraction:perm:pair:isp`) in every dimension.

Let `A` be an object of `μVF^◇[n + 2]`, and `σ`, `σ ∘ τ` two orders, where `τ`
swaps the last two positions: both contract the same two coordinates first, in
opposite orders. Then any standard contractions of `A` in these orders have
`μIsp^db`-related classes.

* `n + 2 = 2` is `Lemma723TwoFinal.lemma_7_23_n2` (for `σ = 1`; the case
  `σ = swap` is the same statement read backwards).
* `n + 2 ≥ 3` (`lemma_7_23_succ`): choose contractions `G'₀`, `G''₀` of `A` in
  the two orders with a common zero-centred normalization, and contractions
  `H'`, `H''` of their first-stage sets. `Lemma723Reduction.reduction_7_23`
  reduces the claim to the two-stage fibre hypothesis, which holds at the good
  points `b` outside the zero set of one nonzero polynomial
  (`FibreGood2.fibreHypothesis2_of_good`). At a good point both fibres are
  classes of standard contractions of the slice of the prepared set, in the two
  orders, and Lemma 7.23 for `n = 2` over `S⟨b⟩` relates them
  (`SliceContractions.fibre_ispRel_at`). The polynomial is the product of the
  good polynomials of the four exceptional sets
  (`TwoDimSlices.stage_exists_good_polynomial2`,
  `FibreRestriction.exists_good_polynomial_or_empty`).

The forms with the hypothesis `h714` are kept; `lemma_7_23` and
`lemma_7_23_succ_proved` discharge it with `Lemma714Reduce.lemma714`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma723General
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FibreObjects
open DiamondIntegral.Section7.KernelBaseChange DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.FibreRestriction DiamondIntegral.Section7.TwoDimSlices
open DiamondIntegral.Section7.Lemma723Reduction DiamondIntegral.Section7.SliceContractions
open DiamondIntegral.Section7.FibreGood2 DiamondIntegral.Section7.PieceCombination
open DiamondIntegral.Section7.Corollary715

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

section Succ
variable {n : ℕ} {A : VFObject (M := M) (T : Set M) (n + 1 + 1 + 1)} {σ : Equiv.Perm (Fin (n + 1 + 1 + 1))}

include V hV hVT hTV hnt hv hΓ in
/-- **The two-stage fibre hypothesis**, for contractions with a common centre. -/
theorem fibreHypothesis2_common (G'₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
    (G''₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form (σ * lastSwap n))
    (hcen : G'₀.normalization.center = G''₀.normalization.center)
    (H' : NormalizedMeasuredContraction (G := G) (firstSet G'₀) (firstForm G'₀) 1)
    (H'' : NormalizedMeasuredContraction (G := G) (firstSet G''₀) (firstForm G''₀) 1) :
    FibreHypothesis2 h00 hc hκ hs hsmall G'₀ H' G''₀ H'' := by
  obtain ⟨P₁, hP₁, hg₁⟩ := stage_exists_good_polynomial2 (m := n + 1) (stage G'₀) hc hs hsmall
  obtain ⟨P₂, hP₂, hg₂⟩ := stage_exists_good_polynomial2 (m := n + 1) (stage G''₀) hc hs hsmall
  obtain ⟨P₃, hP₃, hg₃⟩ := exists_good_polynomial_or_empty hc hs hsmall (stage H').exceptional
    (Or.inl (stage H').exceptional_dim)
  obtain ⟨P₄, hP₄, hg₄⟩ := exists_good_polynomial_or_empty hc hs hsmall (stage H'').exceptional
    (Or.inl (stage H'').exceptional_dim)
  refine fibreHypothesis2_of_good h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ G'₀ H' G''₀ H'' (P₁ * P₂ * P₃ * P₄)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hP₂) hP₃) hP₄) ?_
  intro b hb _
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul] at hb
  have h4 := right_ne_zero_of_mul hb
  have h123 := left_ne_zero_of_mul hb
  have h3 := right_ne_zero_of_mul h123
  have h12 := left_ne_zero_of_mul h123
  have h2 := right_ne_zero_of_mul h12
  have h1 := left_ne_zero_of_mul h12
  have hsm' := adjoin_small hκ hsmall b
  exact ⟨_, _, fibre_ispRel_at h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ G'₀ G''₀ hcen H' H'' b
    (hg₁ b (hTb b) hsm' h1) (hg₂ b (hTb b) hsm' h2) (hg₃ b (hTb b) hsm' h3) (hg₄ b (hTb b) hsm' h4)⟩

include V hV hVT hTV hnt in
/-- **Lemma 7.23 (`contraction:perm:pair:isp`) with at least three VF
coordinates**, on the Lemma 7.14 input. -/
theorem lemma_7_23_succ (h714 : Lemma714 M G) (A : VFObject (M := M) (T : Set M) (n + 1 + 1 + 1))
    {σ : Equiv.Perm (Fin (n + 1 + 1 + 1))}
    (F₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
    (F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form (σ * lastSwap n)) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A F₂) := by
  obtain ⟨D⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A.carrier A.proper
  obtain ⟨G'₀, hG'⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A.carrier A.form (object_levels hv A) σ D
  obtain ⟨G''₀, hG''⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A.carrier A.form (object_levels hv A) (σ * lastSwap n) D
  have hcen : G'₀.normalization.center = G''₀.normalization.center := by rw [hG', hG'']
  have hLev' := restForm_levels hv G'₀.preparedContraction.data
    (preparedForm_levels hc h00 hκ hs hv lin hsmall hΓ (object_levels hv A) G'₀)
  have hLev'' := restForm_levels hv G''₀.preparedContraction.data
    (preparedForm_levels hc h00 hκ hs hv lin hsmall hΓ (object_levels hv A) G''₀)
  obtain ⟨D'⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (firstSet G'₀) (stage G'₀).contracted_proper
  obtain ⟨D''⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (firstSet G''₀) (stage G''₀).contracted_proper
  obtain ⟨H', -⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (firstSet G'₀) (firstForm G'₀) hLev' 1 D'
  obtain ⟨H'', -⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (firstSet G''₀) (firstForm G''₀) hLev'' 1 D''
  exact reduction_7_23 h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ h714 G'₀ G''₀ hcen H' H''
    (fibreHypothesis2_common h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ G'₀ G''₀ hcen H' H'') F₁ F₂

include V hV hVT hTV hnt in
/-- **Lemma 7.23 with at least three VF coordinates**, hypothesis-free. -/
theorem lemma_7_23_succ_proved (A : VFObject (M := M) (T : Set M) (n + 1 + 1 + 1))
    {σ : Equiv.Perm (Fin (n + 1 + 1 + 1))}
    (F₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
    (F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form (σ * lastSwap n)) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A F₂) :=
  lemma_7_23_succ h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ Lemma714Reduce.lemma714 A F₁ F₂

end Succ

/-! ### All dimensions -/

section All

/-- Classes do not depend on how the order is written. -/
theorem clsOf_cast {n : ℕ} (A : VFObject (M := M) (T : Set M) (n + 1)) {e e' : Equiv.Perm (Fin (n + 1))}
    (h : e = e') (F : NormalizedMeasuredContraction (G := G) A.carrier A.form e) :
    clsOf h00 hc hκ hs hv hsmall hΓ A (h ▸ F) = clsOf h00 hc hκ hs hv hsmall hΓ A F := by
  subst h
  rfl

include V hV hVT hTV hnt in
/-- **Lemma 7.23 (`contraction:perm:pair:isp`).** Let `A` be an object of
`μVF^◇[n + 2]` over `S`, and `σ`, `σ ∘ τ` orders, where `τ` swaps the last two
positions. Standard contractions of `A` in the orders `σ` and `σ ∘ τ` have
`μIsp^db`-related classes. -/
theorem lemma_7_23 {n : ℕ} (A : VFObject (M := M) (T : Set M) (n + 1 + 1)) {σ : Equiv.Perm (Fin (n + 1 + 1))}
    (F₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
    (F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form
      (σ * Equiv.swap (Fin.last (n + 1)) (Fin.last n).castSucc)) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A F₂) := by
  cases n with
  | succ n => exact lemma_7_23_succ_proved h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A F₁ F₂
  | zero =>
    have hswap : Equiv.swap (Fin.last (0 + 1)) (Fin.last 0).castSucc = Equiv.swap (0 : Fin 2) 1 :=
      Equiv.swap_comm _ _
    rcases Lemma723TwoFinal.perm_two σ with rfl | rfl
    · have he : (1 : Equiv.Perm (Fin 2)) * Equiv.swap (Fin.last (0 + 1)) (Fin.last 0).castSucc =
          Equiv.swap 0 1 := by rw [one_mul, hswap]
      rw [← clsOf_cast h00 hc hκ hs hv hsmall hΓ A he F₂]
      exact ProvedResults.lemma_7_23_n2 h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A F₁ (he ▸ F₂)
    · have he : Equiv.swap (0 : Fin 2) 1 * Equiv.swap (Fin.last (0 + 1)) (Fin.last 0).castSucc = 1 := by
        rw [hswap, Equiv.swap_mul_self]
      rw [← clsOf_cast h00 hc hκ hs hv hsmall hΓ A he F₂]
      exact ispRel_symm (ProvedResults.lemma_7_23_n2 h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A (he ▸ F₂) F₁)

end All

end DiamondIntegral.Section7.Lemma723General
