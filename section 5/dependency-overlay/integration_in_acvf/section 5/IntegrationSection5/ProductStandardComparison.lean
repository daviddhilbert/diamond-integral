import IntegrationSection5.ProductProgramVolume
import IntegrationSection5.StandardProgramComparison
import IntegrationSection5.CellStandardPresentation

/-! The two actual product programs induce the same quotient and the same
volume tuple after restoring the original coordinate order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {b c : ℕ}

theorem product_program_standard_comparison
    (H : DefSet (M := M) S 2 0) (AD AE : DefSet (M := M) S 1 0)
    (BD : DefSet (M := M) S 1 b) (BE : DefSet (M := M) S 1 c)
    (d : Map AD BD) (e : Map AE BE)
    (P : ProductContractionProgram (G := G) H AD AE BD BE d e)
    (Q : ProductContractionProgram (G := G) (vfPermutationImage H (Equiv.swap 0 1)) AE AD BE BD e d) :
    ∃ C12 : StandardContraction H (Equiv.refl _), ∃ C21 : StandardContraction H (Equiv.swap 0 1),
      Nonempty (C12.contractionObject ≅ C21.contractionObject) := by
  let HS := vfPermutationImage H (Equiv.swap 0 1)
  have hId : H = vfPermutationImage H (Equiv.refl _) := (vfPermutationImage_identity H).symm
  let C12 := standardContractionOfProgram H H (Equiv.refl _) hId P.program
  let C21 := standardContractionOfProgram H HS (Equiv.swap 0 1) rfl Q.program
  let s12 := standardProgramSourceMap H H (Equiv.refl _) hId
  let s21 := standardProgramSourceMap H HS (Equiv.swap 0 1) rfl
  have hD (a : H) : Q.eSource (s21 a) = P.dSource (s12 a) := by
    apply unary_zeroRV_ext
    rw [Q.e_spec,P.d_spec]
    rfl
  have hE (a : H) : Q.dSource (s21 a) = P.eSource (s12 a) := by
    apply unary_zeroRV_ext
    rw [Q.d_spec,P.e_spec]
    rfl
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
  exact ⟨C12,C21,⟨rvIsoOfSurjectiveKernels C12.contractionObject C21.contractionObject
    C12.rawContractionMap C12.rawContractionMap_surjective
    C21.rawContractionMap C21.rawContractionMap_surjective hker hvol⟩⟩

theorem product_swapped_source (D E : Set (VF (M := M))) (H : DefSet (M := M) S 2 0)
    (hH : carrier H = cellPointSet (D ×ˢ E)) :
    carrier (vfPermutationImage H (Equiv.swap 0 1)) = cellPointSet (E ×ˢ D) := by
  ext p
  rw [vfPermutationImage_mem,hH]
  change pointCell (vfPermutation (Equiv.swap (0 : Fin 2) 1).symm p) ∈ D ×ˢ E ↔ pointCell p ∈ E ×ˢ D
  have hSwap : pointCell (vfPermutation (Equiv.swap (0 : Fin 2) 1).symm p) = Prod.swap (pointCell p) := by
    simp only [Equiv.symm_swap,pointCell,vfPermutation,Function.comp_apply,vfAt,
      Equiv.swap_apply_left,Equiv.swap_apply_right,Prod.swap_prod_mk]
  rw [hSwap]
  exact and_comm

theorem product_standard_contractions (D E : Set (VF (M := M)))
    {AD AE : DefSet (M := M) S 1 0} {BD : DefSet (M := M) S 1 b} {BE : DefSet (M := M) S 1 c}
    (hAD : carrier AD = vfUnarySet D) (hAE : carrier AE = vfUnarySet E)
    (d : SpecialBijection AD BD) (e : SpecialBijection AE BE)
    (hd : GammaChainDefinable G d.chain) (he : GammaChainDefinable G e.chain)
    (hBD : IsRVPullback (carrier BD)) (hBE : IsRVPullback (carrier BE))
    (H : DefSet (M := M) S 2 0) (hH : carrier H = cellPointSet (D ×ˢ E))
    (hHG : GammaSetDefinable G (carrier H)) :
    ∃ C12 : StandardContraction H (Equiv.refl _), ∃ C21 : StandardContraction H (Equiv.swap 0 1),
      Nonempty (C12.contractionObject ≅ C21.contractionObject) := by
  obtain ⟨P⟩ := product_contraction_program D E hAD hAE d e hd he hBD hBE H hH hHG
  obtain ⟨Q⟩ := product_contraction_program E D hAE hAD e d he hd hBE hBD
    (vfPermutationImage H (Equiv.swap 0 1)) (product_swapped_source D E H hH)
    (gamma_vfPermutationImage H hHG (Equiv.swap 0 1))
  exact product_program_standard_comparison H AD AE BD BE d.toMap e.toMap P Q

end IntegrationInACVF.Section5
