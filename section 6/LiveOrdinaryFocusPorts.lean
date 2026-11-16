import «section 6».LiveOrdinaryCanonicalFrames

/-! A live ordinary focus extends to the whole current source by using
only its live RV-label locus. Already frozen discs are inactive. Outside
the new core, the actual variable-endpoint map has precisely the ordinary
VF value and every old RV label. -/

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

theorem activeTags_live : (X.liveFrame.activeTags D hD).carrier ⊆ X.liveLabels.carrier := by
  rintro u ⟨p,hp⟩
  obtain ⟨a,ha,hLocus⟩ := p.property
  change p.val.2=u at hp
  have hTags : a.val.2=u := (congrArg Prod.snd ha).trans hp
  exact hTags ▸ a.property.2

def activeInclusion : Map (focusActive X.current (X.liveFrame.activeTags D hD))
    (focusActive X.liveFrame.source (X.liveFrame.activeTags D hD)) :=
  Map.inclusion (fun p hp => ⟨⟨hp.1,X.activeTags_live D hD hp.2⟩,hp.2⟩)

def wholeFocusData : UnaryFocusData X.current where
  activeTags := X.liveFrame.activeTags D hD
  focus := (X.liveFrame.focusData D hD).focus
  focusMap := (X.liveFrame.focusData D hD).focusMap.comp (X.activeInclusion D hD)
  focusMap_eq p := (X.liveFrame.focusData D hD).focusMap_eq (X.activeInclusion D hD p)
  sourceProper := X.proper
  sourceDoublyBounded := X.doublyBounded
  tagged := X.tagged
  focusRV p hp hu :=
    (X.liveFrame.focusData D hD).focusRV p ⟨hp,X.activeTags_live D hD hu⟩ hu

theorem relative_inactive_on_frozen (E : UnaryRelativeApertureData X.current)
    (hActive : E.focusData.activeTags=X.liveFrame.activeTags D hD)
    {p : Mixed M 1 q} (hp : p.2 ∉ X.liveLabels.carrier) : (E.point p).1=p.1 := by
  apply E.point_inactive
  intro he
  exact hp (X.activeTags_live D hD (hActive ▸ he))

theorem relative_field_matches_ordinary (E : UnaryRelativeApertureData X.current)
    (hActive : E.focusData.activeTags=X.liveFrame.activeTags D hD)
    (hFocus : ∀ u,E.focusData.focus u=(X.liveFrame.focusData D hD).focus u)
    (p : focusActive X.current X.liveLabels) (hCore : E.core p.val=false) :
    (E.point p.val).1=(D.toFocusGeometry.eta (X.oldMap p).val).1 := by
  by_cases hu : p.val.2 ∈ (X.liveFrame.activeTags D hD).carrier
  · have hEA : p.val.2 ∈ E.focusData.activeTags.carrier := hActive.symm ▸ hu
    have hLocus : (X.oldMap p).val ∈ D.locus := (X.liveFrame.activeTags_at D hD p).mp hu
    have hFE : E.extendedFocus p.val=D.center (X.oldMap p).val :=
      (E.extendedFocus_active ⟨p.val,p.property.1,hEA⟩).trans
        ((hFocus _).trans (X.liveFrame.focusData_value D hD p hu))
    have hLeft : (E.point p.val).1 0=p.val.1 0-D.center (X.oldMap p).val := by
      simp only [UnaryRelativeApertureData.point,UnaryRelativeApertureData.coordinate,
        Function.update_self,hCore,Bool.false_eq_true,ite_false,add_zero,hFE]
    have hRight : (D.toFocusGeometry.eta (X.oldMap p).val).1 0=
        (X.oldMap p).val.1 0-D.center (X.oldMap p).val := by
      simp only [SpecialTransformations.Section5.FocusGeometry.eta,if_pos hLocus,
        SpecialTransformations.Section5.replace,Function.update_self]
    have hHead := hLeft.trans ((congrArg (fun x => x-D.center (X.oldMap p).val)
      (congrArg (fun z : Mixed M 1 r => z.1 0) (X.point p)).symm).trans hRight.symm)
    funext i
    fin_cases i
    exact hHead
  · have hEA : p.val.2 ∉ E.focusData.activeTags.carrier := fun he => hu (hActive ▸ he)
    have hLocus : (X.oldMap p).val ∉ D.locus :=
      fun he => hu ((X.liveFrame.activeTags_at D hD p).mpr he)
    calc
      (E.point p.val).1=p.val.1 := E.point_inactive hEA
      _=(X.oldMap p).val.1 := (congrArg Prod.fst (X.point p)).symm
      _=(D.toFocusGeometry.eta (X.oldMap p).val).1 := by
        rw [SpecialTransformations.Section5.FocusGeometry.eta,if_neg hLocus]

theorem relative_old_labels (E : UnaryRelativeApertureData X.current)
    (p : focusActive X.current X.liveLabels) :
    (E.point p.val).2 ∘ (fun i => Fin.natAdd 1 (X.labels i))=(X.oldMap p).val.2 := by
  rw [X.point p]
  funext i
  simp only [UnaryRelativeApertureData.point,Function.comp_apply,Fin.append_right]

end DiamondIntegral.Section6.LiveOrdinaryUnaryFrame
