import «section 3».GammaStandardFiniteRestrictionValues
import Integration7.GammaRVLabelCuts

/-! The actual target restrictions of a specified contraction give
finite measured scissors with the whole original Gamma density.
This reuses the proved measured RV finite-partition theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}

theorem gammaStandard_label_partition_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hNames : commonRealNames B ⊆ (C.base : Set M))
    {ι : Type} [Fintype ι] {d : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    (H : ι → SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable B (carrier A)) (hH : ∀ i, GammaSetDefinable B (carrier (H i)))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (hfinH : ∀ i, ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier (H i)}.Finite)
    (ρ : Fin d → Fin a) (R : ι → Set (Point (M := M) 0 d))
    (hR : ∀ i, GammaSetDefinable B (R i))
    (hDisj : ∀ i j, i ≠ j → Disjoint (R i) (R j))
    (hCover : ∀ r : Point (M := M) 0 d, ∃ i, r ∈ R i)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    (P : ∀ i, StandardTargetRestrictionPresentation (G := B) T (H i)
      (rvLabelCut T.target (gamma_program_final_set T.program hT)
        (fun j => suffixIndex T.program.rvArity_le (ρ j)) (R i) (hR i) hNames))
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfinA T hT ω) =
      ∑ i, gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC (hH i) (hfinH i)
        (P i).contraction (P i).gamma ω) := by
  apply gammaStandard_finite_restriction_values C hBC H hA hH hfinA hfinH T hT _ P _ _ _ ω
  · intro i p hp
    exact hp.1
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro p ⟨_,hi⟩ ⟨_,hj⟩
    exact Set.disjoint_left.mp (hDisj i j hij) hi hj
  · intro q
    obtain ⟨i,hi⟩ := hCover (Fin.elim0,q.val.2 ∘ (fun j => suffixIndex T.program.rvArity_le (ρ j)))
    exact ⟨i,q.property,hi⟩


theorem gammaStandard_binary_label_partition_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hNames : commonRealNames B ⊆ (C.base : Set M)) {d : ℕ}
    {A H₀ H₁ : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    (hA : GammaSetDefinable B (carrier A))
    (h₀ : GammaSetDefinable B (carrier H₀)) (h₁ : GammaSetDefinable B (carrier H₁))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (hfin₀ : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier H₀}.Finite)
    (hfin₁ : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier H₁}.Finite)
    (ρ : Fin d → Fin a) (R : Set (Point (M := M) 0 d))
    (hR : GammaSetDefinable B R) (hRC : GammaSetDefinable B (Set.univ \ R))
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    (P₀ : StandardTargetRestrictionPresentation (G := B) T H₀
      (rvLabelCut T.target (gamma_program_final_set T.program hT)
        (fun j => suffixIndex T.program.rvArity_le (ρ j)) R hR hNames))
    (P₁ : StandardTargetRestrictionPresentation (G := B) T H₁
      (rvLabelCut T.target (gamma_program_final_set T.program hT)
        (fun j => suffixIndex T.program.rvArity_le (ρ j)) (Set.univ \ R) hRC hNames))
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfinA T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC h₀ hfin₀ P₀.contraction P₀.gamma ω) +
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC h₁ hfin₁ P₁.contraction P₁.gamma ω) := by
  let H : Fin 2 → SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a := ![H₀,H₁]
  let S : Fin 2 → Set (Point (M := M) 0 d) := ![R,Set.univ \ R]
  have hH : ∀ i, GammaSetDefinable B (carrier (H i)) := by intro i; fin_cases i; exact h₀; exact h₁
  have hF : ∀ i, ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier (H i)}.Finite := by
    intro i; fin_cases i; exact hfin₀; exact hfin₁
  have hS : ∀ i, GammaSetDefinable B (S i) := by intro i; fin_cases i; exact hR; exact hRC
  let P : ∀ i, StandardTargetRestrictionPresentation (G := B) T (H i)
      (rvLabelCut T.target (gamma_program_final_set T.program hT)
        (fun j => suffixIndex T.program.rvArity_le (ρ j)) (S i) (hS i) hNames) :=
    Fin.cases P₀ (fun j => Fin.cases P₁ (fun k => Fin.elim0 k) j)
  have hDisj : ∀ i j : Fin 2, i ≠ j → Disjoint (S i) (S j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · apply Set.disjoint_left.mpr
      intro r hr hs
      exact hs.2 hr
    · apply Set.disjoint_left.mpr
      intro r hs hr
      exact hs.2 hr
    · exact (hij rfl).elim
  have hCover : ∀ r : Point (M := M) 0 d, ∃ i, r ∈ S i := by
    intro r
    by_cases hr : r ∈ R
    · exact ⟨0,hr⟩
    · exact ⟨1,Set.mem_univ _,hr⟩
  have h := gammaStandard_label_partition_values C hBC hNames H hA hH hfinA hF ρ S hS hDisj hCover T hT P ω
  have hP₀ : P 0 = P₀ := rfl
  have hP₁ : P 1 = P₁ := by
    change P ((0 : Fin 1).succ) = P₁
    simp only [P,Fin.cases_succ,Fin.cases_zero]
  simpa only [Fin.sum_univ_two,hP₀,hP₁] using h

end DiamondIntegral.Section3
