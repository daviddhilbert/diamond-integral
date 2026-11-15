import IntegrationSection5.CellStagedContractions
import IntegrationSection5.ProgramStandardPresentation

/-! The two cell programs become standard contractions in the stated
coordinate orders, with the actual volume-coordinate change explicit. -/
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
variable {G : GammaParameters.Base (M := M)} {S R : Set M}

theorem vfPermutationImage_mem (A : DefSet (M := M) S 2 0)
    (σ : Equiv.Perm (Fin 2)) (p : Point (M := M) 2 0) :
    p ∈ carrier (vfPermutationImage A σ) ↔ vfPermutation σ.symm p ∈ carrier A := by
  constructor
  · rintro ⟨a,ha⟩
    change vfPermutation σ a.val = p at ha
    exact (congrArg (vfPermutation σ.symm) ha) ▸
      ((vfPermutation_inverse σ a.val).symm ▸ a.property)
  · intro hp
    refine ⟨⟨vfPermutation σ.symm p,hp⟩,?_⟩
    exact vfPermutation_inverse σ.symm p

theorem cell_swapped_presentation {C : Set (VF (M := M) × VF (M := M))}
    (A B : DefSet (M := M) S 2 0) (hA : carrier A = cellPointSet C)
    (hB : carrier B = cellPointSet (swappedCell C)) :
    B = vfPermutationImage A (Equiv.swap 0 1) := by
  apply PresentedSet.eq_of_carrier_eq
  ext p
  change p ∈ carrier B ↔ p ∈ carrier (vfPermutationImage A (Equiv.swap 0 1))
  rw [vfPermutationImage_mem,hB,hA]
  have hSwap : pointCell (vfPermutation (Equiv.swap (0 : Fin 2) 1).symm p) =
      Prod.swap (pointCell p) := by
    simp only [Equiv.symm_swap,pointCell,vfPermutation,Function.comp_apply,vfAt,
      Equiv.swap_apply_left,Equiv.swap_apply_right,Prod.swap_prod_mk]
  change Prod.swap (pointCell p) ∈ C ↔ pointCell (vfPermutation (Equiv.swap 0 1).symm p) ∈ C
  rw [hSwap]

theorem cell_standard_pair_of_matched
    {C : Set (VF (M := M) × VF (M := M))}
    {A : DefSet (M := M) S 2 0} {B : DefSet (M := M) R 2 0}
    (hA : carrier A = cellPointSet C) (hB : carrier B = cellPointSet (swappedCell C))
    {T : HeadPreparation B} {U : HeadPreparation A}
    (Q : MatchedHeadCompletion (G := G) T U) (e : Q.objectA ≅ Q.objectB) :
    ∃ W : Set M, ∃ AR : DefSet (M := M) W 2 0, carrier AR = cellPointSet C ∧
      ∃ C12 : StandardContraction AR (Equiv.refl _),
      ∃ C21 : StandardContraction AR (Equiv.swap 0 1),
        Nonempty (C12.contractionObject ≅ C21.contractionObject) := by
  let AR := extendBase A Q.containsB
  let BR := extendBase B Q.containsA
  have hId : AR = vfPermutationImage AR (Equiv.refl _) := (vfPermutationImage_identity AR).symm
  have hSwap : BR = vfPermutationImage AR (Equiv.swap 0 1) :=
    cell_swapped_presentation AR BR hA hB
  let C12 := standardContractionOfProgram AR AR (Equiv.refl _) hId Q.programB
  let C21 := standardContractionOfProgram AR BR (Equiv.swap 0 1) hSwap Q.programA
  let e12 := standardProgramVolumeIso AR AR (Equiv.refl _) hId Q.programB
  let e21 := standardProgramVolumeIso AR BR (Equiv.swap 0 1) hSwap Q.programA
  let idIso := @SpecialTransformations.Section4.rvReindexVolumeIso M
    (@CanonicalStructure.normalize M sM) Q.codes 2 Q.objectB (Equiv.refl _)
  let swapIso := @SpecialTransformations.Section4.rvReindexVolumeIso M
    (@CanonicalStructure.normalize M sM) Q.codes 2 Q.objectA (Equiv.swap 0 1)
  refine ⟨Q.codes,AR,hA,C12,C21,?_⟩
  exact ⟨e12.trans (idIso.symm.trans (e.symm.trans (swapIso.trans e21.symm)))⟩

end IntegrationInACVF.Section5
