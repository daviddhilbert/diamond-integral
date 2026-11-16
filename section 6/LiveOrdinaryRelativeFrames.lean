import «section 6».LiveOrdinaryFocusPorts
import «section 6».UnaryRelativeStepMaps

/-! A complete variable-endpoint centripetal transition of a live
ordinary comparison. The actual inverse identifies the new live locus,
old VF values and all old labels. Preparedness of the whole current set
makes its frozen tag complement a full RV-pullback. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
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

def relativeOldMap (E : UnaryRelativeApertureData X.current) (h00 : M ⊨ Axioms.ACVF00) :
    Map (focusActive (regularizeMap E.map.image).image (E.stepLiveTags X.liveLabels))
      (originalBaseOrdinarySet hc D.etaImage
        (OrdinaryUnaryFocusFrame.centripetalTarget_gamma (hA := hA) D hD)) := by
  let L := SpecialTransformations.Section5.gammaLogicInput (ordinaryNamedGammaBase S)
  let oldStep := originalBaseOrdinaryMap hc hA
    (OrdinaryUnaryFocusFrame.centripetalTarget_gamma (hA := hA) D hD)
    (SpecialTransformations.Section5.Primitive.centripetal D).toMap
    (SpecialTransformations.Section5.GammaPrimitiveDefinable.graph L (.centripetal D) ⟨hA,hD⟩)
  exact oldStep.comp (X.oldMap.comp (E.stepLiveInverse h00 X.liveLabels))

theorem relativeOldMap_point (E : UnaryRelativeApertureData X.current) (h00 : M ⊨ Axioms.ACVF00)
    (hActive : E.focusData.activeTags=X.liveFrame.activeTags D hD)
    (hFocus : ∀ u,E.focusData.focus u=(X.liveFrame.focusData D hD).focus u)
    (p : focusActive (regularizeMap E.map.image).image (E.stepLiveTags X.liveLabels)) :
    (X.relativeOldMap D hD E h00 p).val=
      (p.val.1,p.val.2 ∘ (fun i => E.stepOldLabels (X.labels i))) := by
  let a := E.stepLiveInverse h00 X.liveLabels p
  have hp : E.stepPoint a.val=p.val := E.stepLiveInverse_point h00 X.liveLabels p
  have hCore : E.core a.val=false := E.stepLiveInverse_noncore h00 X.liveLabels p
  change (D.toFocusGeometry.eta (X.oldMap a).val)=_
  apply Prod.ext
  · calc
      (D.toFocusGeometry.eta (X.oldMap a).val).1=(E.point a.val).1 :=
        (X.relative_field_matches_ordinary D hD E hActive hFocus a hCore).symm
      _=p.val.1 := congrArg Prod.fst hp
  · rw [D.toFocusGeometry.eta_labels,X.point a]
    have hTail : p.val.2 ∘ E.stepOldLabels=a.val.2 :=
      (congrArg (fun z : Mixed M 1 (1+(1+q)) => z.2 ∘ E.stepOldLabels) hp).symm.trans
        (E.stepOldLabels_at a.val)
    funext i
    exact (congrFun hTail (X.labels i)).symm

theorem relativeOldMap_faithful (E : UnaryRelativeApertureData X.current)
    (h00 : M ⊨ Axioms.ACVF00)
    (hActive : E.focusData.activeTags=X.liveFrame.activeTags D hD)
    (hFocus : ∀ u,E.focusData.focus u=(X.liveFrame.focusData D hD).focus u)
    (p z : focusActive (regularizeMap E.map.image).image (E.stepLiveTags X.liveLabels))
    (hSame : SpecialTransformations.Section5.SameRV
      (X.relativeOldMap D hD E h00 p).val (X.relativeOldMap D hD E h00 z).val) : p.val.2=z.val.2 := by
  let a := E.stepLiveInverse h00 X.liveLabels p
  let b := E.stepLiveInverse h00 X.liveLabels z
  have ha : E.stepPoint a.val=p.val := E.stepLiveInverse_point h00 X.liveLabels p
  have hb : E.stepPoint b.val=z.val := E.stepLiveInverse_point h00 X.liveLabels z
  have haCore : E.core a.val=false := E.stepLiveInverse_noncore h00 X.liveLabels p
  have hbCore : E.core b.val=false := E.stepLiveInverse_noncore h00 X.liveLabels z
  have hOld : SpecialTransformations.Section5.SameRV (X.oldMap a).val (X.oldMap b).val :=
    (SpecialTransformations.Section5.Primitive.centripetal D).sameRV_of (X.oldMap a) (X.oldMap b) hSame
  have hTags : a.val.2=b.val.2 := X.faithful a b hOld
  have hVF := ((ordinary_sameRV_iff _ _).mp hSame).1
  rw [X.relativeOldMap_point D hD E h00 hActive hFocus p,
    X.relativeOldMap_point D hD E h00 hActive hFocus z] at hVF
  have hOut : tupleRV M (E.point a.val).1=tupleRV M (E.point b.val).1 := by
    change tupleRV M (E.stepPoint a.val).1=tupleRV M (E.stepPoint b.val).1
    rw [ha,hb]
    exact hVF
  calc
    p.val.2=(E.stepPoint a.val).2 := (congrArg Prod.snd ha).symm
    _=(E.stepPoint b.val).2 := by
      change Fin.append (tupleRV M (E.point a.val).1) (E.point a.val).2=
        Fin.append (tupleRV M (E.point b.val).1) (E.point b.val).2
      rw [hOut]
      congr 1
      simp only [UnaryRelativeApertureData.point,haCore,hbCore,hTags]
    _=z.val.2 := congrArg Prod.snd hb

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def afterRelativeCentripetal (E : UnaryRelativeApertureData X.current)
    (hPullback : IsRVPullback X.current.carrier)
    (hActive : E.focusData.activeTags=X.liveFrame.activeTags D hD)
    (hFocus : ∀ u,E.focusData.focus u=(X.liveFrame.focusData D hD).focus u)
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) :
    LiveOrdinaryUnaryFrame hc D.etaImage
      (OrdinaryUnaryFocusFrame.centripetalTarget_gamma (hA := hA) D hD) (1+(1+q)) := by
  have hW := E.regularized_image_rvPullback hPullback
  refine {
    current := (regularizeMap E.map.image).image
    liveLabels := E.stepLiveTags X.liveLabels
    oldMap := X.relativeOldMap D hD E h00
    labels := fun i => E.stepOldLabels (X.labels i)
    point := X.relativeOldMap_point D hD E h00 hActive hFocus
    proper := regularization_properInvariant h00 hc hκ hs hv E.map.image
      (E.image_properInvariant h00 hc hκ hs hv hsmall) (E.image_vfDoublyBounded hc hs hsmall)
    doublyBounded := regularized_vfDoublyBounded (E.image_vfDoublyBounded hc hs hsmall)
    tagged := ?_
    faithful := X.relativeOldMap_faithful D hD E h00 hActive hFocus
    frozenPullback := ?_ }
  · rw [regularization_carrier]
    exact regularized_tagged _
  · apply Set.Subset.antisymm _ (subset_rvHull _)
    intro z hz
    obtain ⟨p,⟨hp,hLive⟩,hVF,hRV⟩ := (mem_rvHull_iff _ z).mp hz
    exact ⟨rvPullback_mem_of_sameRV hW hp hVF hRV,
      fun hzLive => hLive (hRV.symm ▸ hzLive)⟩

theorem afterRelativeCentripetal_pullback (E : UnaryRelativeApertureData X.current)
    (hPullback : IsRVPullback X.current.carrier)
    (hActive : E.focusData.activeTags=X.liveFrame.activeTags D hD)
    (hFocus : ∀ u,E.focusData.focus u=(X.liveFrame.focusData D hD).focus u)
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) :
    IsRVPullback (X.afterRelativeCentripetal D hD E hPullback hActive hFocus h00 hκ hs hv hsmall).current.carrier :=
  E.regularized_image_rvPullback hPullback

end DiamondIntegral.Section6.LiveOrdinaryUnaryFrame
