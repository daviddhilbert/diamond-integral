import IntegrationSection5.NonrectangleFiniteProfiles
import IntegrationSection5.VariableUnaryProfiles
import IntegrationSection5.GammaRVPresentations
import IntegrationSection5.GammaCellComparison
import IntegrationSection5.GammaRectangleFamilyComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.NonrectangleMatchedHeads
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}
variable {T : PositionedCellLabelInjection G A}

def profileGammaIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (Q : NonrectangleMatchedHeads T) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    GammaRVIso G
      (@rvUnaryProfileObject M (@CanonicalStructure.normalize M sM) Q.unary.codes
        (pullbackObject Q.unary.targetA) Q.profileA)
      (@rvUnaryProfileObject M (@CanonicalStructure.normalize M sM) Q.unary.codes
        (pullbackObject Q.unary.targetB) Q.profileB) := by
  have hz (r : RV (M := M)) : r.val = iRVZero ↔ r = rv (0 : VF (M := M)) := by
    have h0 : (rv (0 : VF (M := M))).val = iRVZero := (CanonicalRV.encodedRv_zero_iff _).mpr rfl
    exact ⟨fun h => Subtype.ext (h.trans h0.symm),fun h => (congrArg Subtype.val h).trans h0⟩
  have hForward : ∀ a, ((Q.profileA a).val 0).val = iRVZero ↔
      ((Q.profileB (unaryIsoHomMap Q.unary.iso a)).val 0).val = iRVZero :=
    fun a => (hz _).trans ((Q.profile_zero_iff δ hδ a).trans (hz _).symm)
  have hBack : ∀ b, ((Q.profileB b).val 0).val = iRVZero ↔
      ((Q.profileA (unaryIsoInvMap Q.unary.iso b)).val 0).val = iRVZero := by
    intro b
    have hh : unaryIsoHomMap Q.unary.iso (unaryIsoInvMap Q.unary.iso b) = b := by
      exact congrArg (fun F : @SpecialTransformations.Section4.RVHom M
        (@CanonicalStructure.normalize M sM) Q.unary.codes 1
        (pullbackObject Q.unary.targetB) (pullbackObject Q.unary.targetB) =>
        (@SpecialTransformations.Section4.RVHom.map M (@CanonicalStructure.normalize M sM)
          Q.unary.codes 1 (pullbackObject Q.unary.targetB) (pullbackObject Q.unary.targetB) F) b)
          Q.unary.iso.inv_hom_id
    have h := hForward (unaryIsoInvMap Q.unary.iso b)
    rw [hh] at h
    exact h.symm
  exact ⟨@rvVariableUnaryProfileIso M (@CanonicalStructure.normalize M sM) Q.unary.codes
    (pullbackObject Q.unary.targetA) (pullbackObject Q.unary.targetB) Q.unary.iso
    Q.profileA Q.profileB Q.profileA_one Q.profileB_one hForward hBack
    (Q.profile_hom_first_finite hκ hs hsmall δ hδ) (Q.profile_inv_first_finite hκ hs hsmall δ hδ),
    Q.unary.hom_graph,Q.unary.inv_graph⟩

def gammaRVIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (Q : NonrectangleMatchedHeads T) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    GammaRVIso G Q.completion.objectA Q.completion.objectB :=
  (gammaUnaryHeadVolumeIso Q.unary.targetA Q.completion.targetA_gamma Q.completion.programA.volumeIndex).trans
    ((Q.profileGammaIso hκ hs hsmall δ hδ).trans
      (gammaUnaryHeadVolumeIso Q.unary.targetB Q.completion.targetB_gamma Q.completion.programB.volumeIndex).symm)

def standardComparison {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (Q : NonrectangleMatchedHeads T) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    GammaMixedStandardComparison G (nonrectangleFamilyBranch T.target) := by
  let e12 := gammaStandardProgramVolumeIso Q.source Q.source (Equiv.refl _)
    (vfPermutationImage_identity Q.source).symm Q.completion.programA Q.programA_gamma
  let e21 := gammaStandardProgramVolumeIso Q.source Q.sourceSwapped (Equiv.swap 0 1)
    Q.source_swapped_presentation Q.completion.programB Q.programB_gamma
  let idIso := GammaRVIso.reindexVolume Q.completion.objectA (Equiv.refl _)
    (gamma_unary_head_domain Q.unary.targetA Q.completion.targetA_gamma)
  let swapIso := GammaRVIso.reindexVolume Q.completion.objectB (Equiv.swap 0 1)
    (gamma_unary_head_domain Q.unary.targetB Q.completion.targetB_gamma)
  exact {
    codes := Q.unary.codes
    real_contains := Q.unary.real_contains
    source := Q.source
    source_eq := Q.source_eq
    source_gamma := Q.source_eq.symm ▸ nonrectangleFamilyBranch_gamma T.target
      (T.iso.target_definable (gammaLogicInput G))
    contraction12 := Q.contraction12
    contraction21 := Q.contraction21
    program12_gamma := Q.contraction12_gamma
    program21_gamma := Q.contraction21_gamma
    comparison := e12.trans (idIso.symm.trans ((Q.gammaRVIso hκ hs hsmall δ hδ).trans
      (swapIso.trans e21.symm))) }

end IntegrationInACVF.Section5.PositionedCellLabelInjection.NonrectangleMatchedHeads

namespace IntegrationInACVF.Section5.PositionedCellLabelInjection
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}

theorem nonrectangle_standard_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (T : PositionedCellLabelInjection G A) :
    Nonempty (GammaMixedStandardComparison G (nonrectangleFamilyBranch T.target)) := by
  obtain ⟨Q⟩ := T.nonrectangle_matched_heads hκ hs h00 hsmall δ hδ hδ1 F
  exact ⟨Q.standardComparison hκ hs hsmall δ hδ1⟩

end IntegrationInACVF.Section5.PositionedCellLabelInjection
