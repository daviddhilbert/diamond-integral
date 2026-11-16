import «section 6».OrdinaryNoCoreFocusStep

/-! The constructed unexceptional finite-aperture step has exactly the
ordinary component's VF map and passes every old RV label through its
new branch tag. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.OrdinaryUnaryFocusFrame
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r q : ℕ}
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}
variable (X : OrdinaryUnaryFocusFrame hc A hA q) {j : Fin r}
variable (D : SpecialTransformations.Section5.Focus A 0 j)
variable (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D)
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem component_field_matches_ordinary (E : CentripetalData (G := G) X.source)
    (hCoord : E.coordinate=0) (hActive : E.activeTags=X.activeTags D hD)
    (hFocus : ∀ x u,E.focus x u=(X.focusData D hD).focus u)
    (hCore : ∀ p ∈ X.source.carrier,E.core p=false) (p : X.source) :
    (E.point p.val).1=(D.toFocusGeometry.eta (X.oldMap p).val).1 := by
  by_cases hu : p.val.2 ∈ (X.activeTags D hD).carrier
  · have hEA : p.val.2 ∈ E.activeTags.carrier := hActive.symm ▸ hu
    have hLocus := (X.activeTags_at D hD p).mp hu
    have hFE : E.extendedFocus p.val=D.center (X.oldMap p).val :=
      (E.extendedFocus_active p.property hEA).trans ((hFocus _ _).trans (X.focusData_value D hD p hu))
    have hLeft : (E.point p.val).1 0=p.val.1 0-D.center (X.oldMap p).val := by
      simp only [CentripetalData.point,hCoord,hCore p.val p.property,Bool.false_eq_true,if_false,add_zero]
      change Function.update p.val.1 (0 : Fin 1) (p.val.1 0-E.extendedFocus p.val) (0 : Fin 1)=_
      rw [Function.update_self,hFE]
    have hRight : (D.toFocusGeometry.eta (X.oldMap p).val).1 0=
        (X.oldMap p).val.1 0-D.center (X.oldMap p).val := by
      simp only [SpecialTransformations.Section5.FocusGeometry.eta,if_pos hLocus,
        SpecialTransformations.Section5.replace,Function.update_self]
    have hHead := hLeft.trans ((congrArg (fun x => x-D.center (X.oldMap p).val)
      (congrArg (fun z : Mixed M 1 r => z.1 0) (X.point p)).symm).trans hRight.symm)
    funext i
    fin_cases i
    exact hHead
  · have hEA : p.val.2 ∉ E.activeTags.carrier := fun he => hu (hActive ▸ he)
    have hLocus : (X.oldMap p).val ∉ D.locus := fun he => hu ((X.activeTags_at D hD p).mpr he)
    calc
      (E.point p.val).1=p.val.1 := E.point_inactive hEA
      _=(X.oldMap p).val.1 := (congrArg Prod.fst (X.point p)).symm
      _=(D.toFocusGeometry.eta (X.oldMap p).val).1 := by
        rw [SpecialTransformations.Section5.FocusGeometry.eta,if_neg hLocus]

theorem component_old_labels (E : CentripetalData (G := G) X.source) (p : X.source) :
    (E.point p.val).2 ∘ (fun i => Fin.natAdd 1 (X.labels i))=(X.oldMap p).val.2 := by
  rw [X.point p]
  funext i
  simp only [CentripetalData.point,Function.comp_apply,Fin.append_right]

end DiamondIntegral.Section6.OrdinaryUnaryFocusFrame
