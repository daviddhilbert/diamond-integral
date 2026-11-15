import IntegrationSection5.GammaStandardProgramGraphs
import IntegrationSection5.GammaMatchedHeadRV
import IntegrationSection5.CellStandardPresentation

/-! A complete original-base certificate for a cell comparison: actual
standard programs and an actual RV[2] iso, with every full graph retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S R : Set M} {n m l : ℕ}

def gammaStandardProgramVolumeIso (A B : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n))
    (hB : B = vfPermutationImage A σ) {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S B U) (hT : GammaProgramDefinable G T) :
    GammaRVIso G (standardContractionOfProgram A B σ hB T).contractionObject
      (@SpecialTransformations.Section4.RVObject.reindexVolume M
        (@CanonicalStructure.normalize M sM) S n n T.contractionObject σ.symm) := by
  cases hB
  let C : StandardContraction A σ := ⟨l,U,T⟩
  have hDomain := C.gamma_rv_domain (gamma_program_final_set T hT)
  exact GammaRVIso.ofVolumePreserving (Map.id _) Function.bijective_id (fun _ => rfl)
    (gamma_rvMap_identity_values _ (fun _ => rfl) hDomain)

structure GammaCellStandardComparison (G : GammaParameters.Base (M := M))
    (C : Set (VF (M := M) × VF (M := M))) where
  codes : Set M
  real_contains : G.real ⊆ codes
  source : DefSet (M := M) codes 2 0
  source_eq : carrier source = cellPointSet C
  source_gamma : GammaSetDefinable G (carrier source)
  contraction12 : StandardContraction source (Equiv.refl _)
  contraction21 : StandardContraction source (Equiv.swap 0 1)
  program12_gamma : GammaProgramDefinable G contraction12.program
  program21_gamma : GammaProgramDefinable G contraction21.program
  comparison : GammaRVIso G contraction12.contractionObject contraction21.contractionObject

theorem gamma_cell_pair_of_matched
    {C : Set (VF (M := M) × VF (M := M))}
    {A : DefSet (M := M) S 2 0} {B : DefSet (M := M) R 2 0}
    (hGA : G.real ⊆ S) (hA : carrier A = cellPointSet C)
    (hB : carrier B = cellPointSet (swappedCell C)) (hAG : GammaSetDefinable G (carrier A))
    {T : HeadPreparation B} {U : HeadPreparation A}
    (hTG : GammaGraphDefinable G (pointMapGraph T.map)) (hTtarget : GammaSetDefinable G (carrier T.target))
    (hUG : GammaGraphDefinable G (pointMapGraph U.map)) (hUtarget : GammaSetDefinable G (carrier U.target))
    (Q : MatchedHeadCompletion (G := G) T U) (e : GammaRVIso G Q.objectA Q.objectB) :
    Nonempty (GammaCellStandardComparison G C) := by
  let AR := extendBase A Q.containsB
  let BR := extendBase B Q.containsA
  have hId : AR = vfPermutationImage AR (Equiv.refl _) := (vfPermutationImage_identity AR).symm
  have hSwap : BR = vfPermutationImage AR (Equiv.swap 0 1) := cell_swapped_presentation AR BR hA hB
  let C12 := standardContractionOfProgram AR AR (Equiv.refl _) hId Q.programB
  let C21 := standardContractionOfProgram AR BR (Equiv.swap 0 1) hSwap Q.programA
  have hPA := Q.programA_gamma hTG hTtarget
  have hPB := Q.programB_gamma hUG hUtarget
  let e12 := gammaStandardProgramVolumeIso AR AR (Equiv.refl _) hId Q.programB hPB
  let e21 := gammaStandardProgramVolumeIso AR BR (Equiv.swap 0 1) hSwap Q.programA hPA
  let idIso := GammaRVIso.reindexVolume Q.objectB (Equiv.refl _)
    (gamma_unary_head_domain Q.targetB Q.targetB_gamma)
  let swapIso := GammaRVIso.reindexVolume Q.objectA (Equiv.swap 0 1)
    (gamma_unary_head_domain Q.targetA Q.targetA_gamma)
  exact ⟨{
    codes := Q.codes
    real_contains := fun _ hx => Q.containsB (hGA hx)
    source := AR
    source_eq := hA
    source_gamma := hAG
    contraction12 := C12
    contraction21 := C21
    program12_gamma := standardProgram_program_gamma AR AR (Equiv.refl _) hId Q.programB hPB
    program21_gamma := standardProgram_program_gamma AR BR (Equiv.swap 0 1) hSwap Q.programA hPA
    comparison := e12.trans (idIso.symm.trans (e.symm.trans (swapIso.trans e21.symm))) }⟩

end IntegrationInACVF.Section5
