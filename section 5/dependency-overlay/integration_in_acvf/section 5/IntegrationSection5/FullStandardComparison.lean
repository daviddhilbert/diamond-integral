import IntegrationSection5.FinalNativeComparison
import IntegrationSection5.GammaCellComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductNComparison
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}
open SpecialTransformations.Section3
variable {δ : Values.Gamma (M := M)} {hδ : 1 < δ}

def full_standard_comparison (Z : CommonProductNComparison T δ hδ) : GammaMixedStandardComparison G T.target := by
  let Q := Z.matching
  let X := extendBase (Q.first.left.extendBase Q.first.containsLeft).source Q.contains
  let Y := extendBase (Q.first.right.extendBase Q.first.containsRight).source Q.contains
  have hX : carrier X = T.target := Q.first.left.source_eq
  have hY : carrier Y = T.swappedTarget := Q.first.right.source_eq
  have hSwap : Y = vfPermutationImage X (Equiv.swap 0 1) := by
    apply PresentedSet.eq_of_carrier_eq
    ext p
    rw [vfPermutationImage_mem_mixed,Equiv.symm_swap]
    change (p ∈ carrier Y) ↔ vfPermutation (Equiv.swap 0 1) p ∈ carrier X
    exact (Set.ext_iff.mp hY p).trans (Set.ext_iff.mp hX (vfPermutation (Equiv.swap 0 1) p)).symm
  have hId : X = vfPermutationImage X (Equiv.refl _) := (vfPermutationImage_identity X).symm
  let e12 := gammaStandardProgramVolumeIso X X (Equiv.refl _) hId (Q.leftProgram Z.left) (Q.leftProgram_gamma Z.left)
  let e21 := gammaStandardProgramVolumeIso X Y (Equiv.swap 0 1) hSwap (Q.rightProgram Z.right) (Q.rightProgram_gamma Z.right)
  let idIso := GammaRVIso.reindexVolume (Q.leftProgram Z.left).contractionObject (Equiv.refl _)
    (gamma_unary_head_domain (Q.leftTail Z.left).target (Q.leftTail_target_gamma Z.left))
  let swapIso := GammaRVIso.reindexVolume (Q.rightProgram Z.right).contractionObject (Equiv.swap 0 1)
    (gamma_unary_head_domain (Q.rightTail Z.right).target (Q.rightTail_target_gamma Z.right))
  exact {
    codes := Q.unary.codes
    real_contains := Q.unary.real_contains
    source := X
    source_eq := hX
    source_gamma := hX.symm ▸ T.iso.target_definable (gammaLogicInput G)
    contraction12 := standardContractionOfProgram X X (Equiv.refl _) hId (Q.leftProgram Z.left)
    contraction21 := standardContractionOfProgram X Y (Equiv.swap 0 1) hSwap (Q.rightProgram Z.right)
    program12_gamma := standardProgram_program_gamma X X (Equiv.refl _) hId (Q.leftProgram Z.left) (Q.leftProgram_gamma Z.left)
    program21_gamma := standardProgram_program_gamma X Y (Equiv.swap 0 1) hSwap (Q.rightProgram Z.right) (Q.rightProgram_gamma Z.right)
    comparison := e12.trans (idIso.symm.trans (Z.full_native_program_comparison.trans (swapIso.trans e21.symm))) }

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductNComparison

namespace IntegrationInACVF.Section5.PositionedCellLabelInjection
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)}
open SpecialTransformations.Section3

theorem full_standard_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (T : PositionedCellLabelInjection G A) : Nonempty (GammaMixedStandardComparison G T.target) := by
  obtain ⟨Z⟩ := T.common_product_n_comparison hκ hs h00 hsmall δ hδ hδ1 F
  exact ⟨Z.full_standard_comparison⟩

end IntegrationInACVF.Section5.PositionedCellLabelInjection
