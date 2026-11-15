import IntegrationSection5.SharedRVProductProgram
import IntegrationSection5.GammaProductCellComparison

/-! Actual standard contractions in both orders for a shared-parameter product, with a full original-Gamma RV[2] comparison. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {m b c : ℕ}
theorem sharedRV_product_program_gamma_comparison
    (H : DefSet (M := M) S 2 m) (hHG : GammaSetDefinable G (carrier H))
    (AD AE : DefSet (M := M) S 1 m)
    (BD : DefSet (M := M) S 1 b) (BE : DefSet (M := M) S 1 c)
    (d : Map AD BD) (e : Map AE BE)
    (P : SharedRVProductProgram (G := G) H AD AE BD BE d e)
    (Q : SharedRVProductProgram (G := G) (vfPermutationImage H (Equiv.swap 0 1)) AE AD BE BD e d) :
    ∃ C12 : StandardContraction H (Equiv.refl _), ∃ C21 : StandardContraction H (Equiv.swap 0 1),
      GammaProgramDefinable G C12.program ∧ GammaProgramDefinable G C21.program ∧
      Nonempty (GammaRVIso G C12.contractionObject C21.contractionObject) := by
  let HS := vfPermutationImage H (Equiv.swap 0 1)
  have hId : H = vfPermutationImage H (Equiv.refl _) := (vfPermutationImage_identity H).symm
  let C12 := standardContractionOfProgram H H (Equiv.refl _) hId P.program
  let C21 := standardContractionOfProgram H HS (Equiv.swap 0 1) rfl Q.program
  let s12 := standardProgramSourceMap H H (Equiv.refl _) hId
  let s21 := standardProgramSourceMap H HS (Equiv.swap 0 1) rfl
  have hD (a : H) : Q.eSource (s21 a) = P.dSource (s12 a) := by
    apply Subtype.ext
    rw [Q.e_spec,P.d_spec]
    apply Prod.ext
    · funext j; fin_cases j; rfl
    · rfl
  have hE (a : H) : Q.dSource (s21 a) = P.eSource (s12 a) := by
    apply Subtype.ext
    rw [Q.d_spec,P.e_spec]
    apply Prod.ext
    · funext j; fin_cases j; rfl
    · rfl
  have hker (a b : H) : C12.rawContractionMap a = C12.rawContractionMap b ↔
      C21.rawContractionMap a = C21.rawContractionMap b := by
    rw [standardProgram_kernel H H (Equiv.refl _) hId P.program,
      standardProgram_kernel H HS (Equiv.swap 0 1) rfl Q.program,
      P.kernel_formula,Q.kernel_formula]
    change (SameRV (d (P.dSource (s12 a))).val (d (P.dSource (s12 b))).val ∧
      SameRV (e (P.eSource (s12 a))).val (e (P.eSource (s12 b))).val) ↔ _
    rw [hE a,hE b,hD a,hD b]
    exact and_comm
  have hvol (a : H) : (rvObjectVolume C21.contractionObject (C21.rawContractionMap a)).val =
      (rvObjectVolume C12.contractionObject (C12.rawContractionMap a)).val := by
    rw [standardProgram_volume H HS (Equiv.swap 0 1) rfl Q.program,
      standardProgram_volume H H (Equiv.refl _) hId P.program,
      Q.volume_formula,P.volume_formula]
    change (![rv (vfAt (e (Q.dSource (s21 a))).val 0),rv (vfAt (d (Q.eSource (s21 a))).val 0)] ∘
      (Equiv.swap (0 : Fin 2) 1).symm) =
        ![rv (vfAt (d (P.dSource (s12 a))).val 0),rv (vfAt (e (P.eSource (s12 a))).val 0)] ∘ (Equiv.refl _).symm
    rw [hE a,hD a]
    funext j
    fin_cases j <;> simp
  have h12 := standardProgram_gamma_graph H H (Equiv.refl _) hId P.program hHG P.gamma_program
  have h21 := standardProgram_gamma_graph H HS (Equiv.swap 0 1) rfl Q.program hHG Q.gamma_program
  exact ⟨C12,C21,
    standardProgram_program_gamma H H (Equiv.refl _) hId P.program P.gamma_program,
    standardProgram_program_gamma H HS (Equiv.swap 0 1) rfl Q.program Q.gamma_program,
    ⟨gammaRVIsoOfSurjectiveKernels C12.contractionObject C21.contractionObject
      C12.rawContractionMap C12.rawContractionMap_surjective C21.rawContractionMap C21.rawContractionMap_surjective
      hker hvol (C12.gamma_raw_output h12) (C21.gamma_raw_output h21)⟩⟩

end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {m b c : ℕ}

theorem vfPermutationImage_mem_mixed (A : DefSet (M := M) S 2 m)
    (σ : Equiv.Perm (Fin 2)) (p : Point (M := M) 2 m) :
    p ∈ carrier (vfPermutationImage A σ) ↔ vfPermutation σ.symm p ∈ carrier A := by
  constructor
  · rintro ⟨a,ha⟩
    change vfPermutation σ a.val = p at ha
    exact (congrArg (vfPermutation σ.symm) ha) ▸
      ((vfPermutation_inverse σ a.val).symm ▸ a.property)
  · intro hp
    refine ⟨⟨vfPermutation σ.symm p,hp⟩,?_⟩
    exact vfPermutation_inverse σ.symm p

theorem sharedRV_product_swapped_source (AD AE : DefSet (M := M) S 1 m)
    (H : DefSet (M := M) S 2 m)
    (hH : carrier H = {p | activeUnaryProjection 0 id p ∈ carrier AD ∧
      activeUnaryProjection 1 id p ∈ carrier AE}) :
    carrier (vfPermutationImage H (Equiv.swap 0 1)) =
      {p | activeUnaryProjection 0 id p ∈ carrier AE ∧ activeUnaryProjection 1 id p ∈ carrier AD} := by
  ext p
  rw [vfPermutationImage_mem_mixed,hH]
  have h0 : activeUnaryProjection 0 id (vfPermutation (Equiv.swap (0 : Fin 2) 1).symm p) =
      activeUnaryProjection 1 id p := by
    apply Prod.ext
    · funext j; fin_cases j
      simp only [activeUnaryProjection,vfPermutation,Function.comp_apply,vfAt,Equiv.symm_swap,Equiv.swap_apply_left]
    · rfl
  have h1 : activeUnaryProjection 1 id (vfPermutation (Equiv.swap (0 : Fin 2) 1).symm p) =
      activeUnaryProjection 0 id p := by
    apply Prod.ext
    · funext j; fin_cases j
      simp only [activeUnaryProjection,vfPermutation,Function.comp_apply,vfAt,Equiv.symm_swap,Equiv.swap_apply_right]
    · rfl
  change (activeUnaryProjection 0 id (vfPermutation (Equiv.swap (0 : Fin 2) 1).symm p) ∈ carrier AD ∧
    activeUnaryProjection 1 id (vfPermutation (Equiv.swap (0 : Fin 2) 1).symm p) ∈ carrier AE) ↔ _
  rw [h0,h1]
  exact and_comm

theorem sharedRV_product_standard_contractions
    {AD AE : DefSet (M := M) S 1 m}
    {BD : DefSet (M := M) S 1 b} {BE : DefSet (M := M) S 1 c}
    (d : SpecialBijection AD BD) (e : SpecialBijection AE BE)
    (hd : GammaChainDefinable G d.chain) (he : GammaChainDefinable G e.chain)
    (hBD : IsRVPullback (carrier BD)) (hBE : IsRVPullback (carrier BE))
    (H : DefSet (M := M) S 2 m)
    (hH : carrier H = {p | activeUnaryProjection 0 id p ∈ carrier AD ∧
      activeUnaryProjection 1 id p ∈ carrier AE})
    (hHG : GammaSetDefinable G (carrier H)) :
    ∃ C12 : StandardContraction H (Equiv.refl _), ∃ C21 : StandardContraction H (Equiv.swap 0 1),
      GammaProgramDefinable G C12.program ∧ GammaProgramDefinable G C21.program ∧
      Nonempty (GammaRVIso G C12.contractionObject C21.contractionObject) := by
  obtain ⟨P⟩ := sharedRV_product_contraction_program d e hd he hBD hBE H hH hHG
  obtain ⟨Q⟩ := sharedRV_product_contraction_program e d he hd hBE hBD
    (vfPermutationImage H (Equiv.swap 0 1)) (sharedRV_product_swapped_source AD AE H hH)
    (gamma_vfPermutationImage H hHG (Equiv.swap 0 1))
  exact sharedRV_product_program_gamma_comparison H hHG AD AE BD BE d.toMap e.toMap P Q

end IntegrationInACVF.Section5
