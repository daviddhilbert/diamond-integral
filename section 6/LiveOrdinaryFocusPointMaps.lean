import «section 6».LiveOrdinaryRelativeFrames
import «section 6».UnaryFocusPointMaps

/-! The actual live focus point, and its ordinary zero event. Pulling
this map back through a whole preparation will select an original
exceptional centre with its full original-base graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.LiveOrdinaryUnaryFrame
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r q : ℕ}
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}
variable (X : LiveOrdinaryUnaryFrame hc A hA q) {j : Fin r}
variable (D : SpecialTransformations.Section5.Focus A 0 j)
variable (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D)

def liveFocusPointMap (hPullback : IsRVPullback X.current.carrier) :
    Map (focusActive X.current (X.wholeFocusData D hD).activeTags) X.liveFrame.source := by
  let F := X.wholeFocusData D hD
  let f := F.focusPointMap hPullback
  refine f.corestrict (fun p => ?_)
  refine ⟨(f p).property,?_⟩
  have he := congrArg Prod.snd (F.focusPointMap_value hPullback p)
  rw [he]
  exact X.activeTags_live D hD p.property.2

theorem liveFocusPointMap_value (hPullback : IsRVPullback X.current.carrier)
    (p : focusActive X.current (X.wholeFocusData D hD).activeTags) :
    (X.liveFocusPointMap D hD hPullback p).val=
      ((fun _ : Fin 1 => (X.wholeFocusData D hD).focus p.val.2),p.val.2) :=
  (X.wholeFocusData D hD).focusPointMap_value hPullback p

theorem liveFocusPointMap_same_labels (hPullback : IsRVPullback X.current.carrier)
    (p z : focusActive X.current (X.wholeFocusData D hD).activeTags) (hTags : p.val.2=z.val.2) :
    X.liveFocusPointMap D hD hPullback p=X.liveFocusPointMap D hD hPullback z := by
  apply Subtype.ext
  exact (X.liveFocusPointMap_value D hD hPullback p).trans
    ((congrArg (fun u => ((fun _ : Fin 1 => (X.wholeFocusData D hD).focus u),u)) hTags).trans
      (X.liveFocusPointMap_value D hD hPullback z).symm)

theorem liveFocusPointMap_ordinary_zero (hPullback : IsRVPullback X.current.carrier)
    (p : focusActive X.current (X.wholeFocusData D hD).activeTags) :
    (D.toFocusGeometry.eta (X.oldMap (X.liveFocusPointMap D hD hPullback p)).val).1 0=(0 : VF M) := by
  let a := X.liveFocusPointMap D hD hPullback p
  have hPoint := X.liveFocusPointMap_value D hD hPullback p
  have hTags := congrArg (fun z : Mixed M 1 q => z.2) hPoint
  change a.val.2=p.val.2 at hTags
  have hu : a.val.2 ∈ (X.liveFrame.activeTags D hD).carrier := by
    rw [hTags]
    exact p.property.2
  have hLocus : (X.oldMap a).val ∈ D.locus := (X.liveFrame.activeTags_at D hD a).mp hu
  have hCenter : (X.liveFrame.focusData D hD).focus a.val.2=D.center (X.oldMap a).val :=
    X.liveFrame.focusData_value D hD a hu
  have hField : (X.oldMap a).val.1 0=(X.liveFrame.focusData D hD).focus a.val.2 := by
    have hF := congrArg (fun z : Mixed M 1 q => z.1 0) hPoint
    change a.val.1 0=(X.wholeFocusData D hD).focus p.val.2 at hF
    exact (congrArg (fun z : Mixed M 1 r => z.1 0) (X.point a)).trans
      (hF.trans (congrArg (X.wholeFocusData D hD).focus hTags.symm))
  change (D.toFocusGeometry.eta (X.oldMap a).val).1 0=(0 : VF M)
  simp only [SpecialTransformations.Section5.FocusGeometry.eta,if_pos hLocus,
    SpecialTransformations.Section5.replace,Function.update_self,hField,← hCenter,sub_self]

end DiamondIntegral.Section6.LiveOrdinaryUnaryFrame
