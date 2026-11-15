import IntegrationSection5.CommonProductPaddedTails
import IntegrationSection5.PaddedBranchProfileIso
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}
namespace GammaRVIso
variable {S : Set M} {n : ℕ}
variable {U V W : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S n}
def castTarget (e : GammaRVIso G U V) (h : V = W) : GammaRVIso G U W := by cases h; exact e
end GammaRVIso

namespace PositionedCellLabelInjection.CommonProductMatching
variable {m : ℕ} {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}
variable {δ : Values.Gamma (M := M)} {hδ : 1 < δ}

theorem old_profileA_eq (Q : CommonProductMatching T δ hδ) :
    selectedVolumeObject (Map.image (rawKeyMap Q.unary.targetA))
      ![Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le Q.unary.specialA.chain) 0),0] =
    @rvUnaryProfileObject M (@CanonicalStructure.normalize M sM) Q.unary.codes
      (pullbackObject Q.unary.targetA) Q.asOld.profileA := by
  change selectedVolumeObject _ _ = selectedVolumeObject _ Q.asOld.completion.programA.volumeIndex
  congr 1
  funext i
  fin_cases i
  · change _ = Q.asOld.completion.programA.volumeIndex 0
    rw [Q.asOld.completion.volumeIndexA_zero]
    apply Fin.ext
    rfl
  · change _ = Q.asOld.completion.programA.volumeIndex 1
    exact Q.asOld.completion.volumeIndexA_one.symm

theorem old_profileB_eq (Q : CommonProductMatching T δ hδ) :
    selectedVolumeObject (Map.image (rawKeyMap Q.unary.targetB))
      ![Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le Q.unary.specialB.chain) 0),0] =
    @rvUnaryProfileObject M (@CanonicalStructure.normalize M sM) Q.unary.codes
      (pullbackObject Q.unary.targetB) Q.asOld.profileB := by
  change selectedVolumeObject _ _ = selectedVolumeObject _ Q.asOld.completion.programB.volumeIndex
  congr 1
  funext i
  fin_cases i
  · change _ = Q.asOld.completion.programB.volumeIndex 0
    rw [Q.asOld.completion.volumeIndexB_zero]
    apply Fin.ext
    rfl
  · change _ = Q.asOld.completion.programB.volumeIndex 1
    exact Q.asOld.completion.volumeIndexB_one.symm

def padded_nonrectangle_profile_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (Q : CommonProductMatching T δ hδ)
    (L : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none)
    (R : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    GammaRVIso G
      (selectedVolumeObject (Map.image (rawKeyMap L.lift.active_image))
        ![Fin.natAdd 1 (suffixIndex L.lift.arity_le ((Fin.natAdd 1 ∘ Q.leftProjection) 0)),0])
      (selectedVolumeObject (Map.image (rawKeyMap R.lift.active_image))
        ![Fin.natAdd 1 (suffixIndex R.lift.arity_le ((Fin.natAdd 1 ∘ Q.rightProjection) 0)),0]) :=
  ((L.lift.profileIso 0).castTarget Q.old_profileA_eq).trans
    ((Q.asOld.profileGammaIso hκ hs hsmall δ hδ).trans ((R.lift.profileIso 0).castTarget Q.old_profileB_eq).symm)

end PositionedCellLabelInjection.CommonProductMatching
end IntegrationInACVF.Section5
