import «section 6».OrdinaryFocusValueBounds

/-! Zero points are fixed even by an active ordinary focus. Together
with the finite focus-value bound this gives identity on an entire
sufficiently small zero neighborhood, including the center. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.OriginalBaseOrdinaryFocus
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r} {j : Fin r}
variable (D : SpecialTransformations.Section5.Focus A 0 j)

theorem eta_fixes_zero (p : A) (hp0 : p.val.1 0=(0 : VF M)) :
    ((SpecialTransformations.Section5.Primitive.centripetal D).toMap p).val=p.val := by
  change D.toFocusGeometry.eta p.val=p.val
  by_cases hp : p.val ∈ D.locus
  · have hRV := D.toFocusGeometry.center_sameRV p.val ⟨p.property,hp⟩
    have hc0 : D.center p.val=(0 : VF M) := (SpecialTransformations.Section5.rv_eq_zero_iff _).mp (by
      simpa only [hp0] using hRV)
    rw [SpecialTransformations.Section5.FocusGeometry.eta,ite_eq_left hp,hc0,sub_zero]
    change (Function.update p.val.1 (0 : Fin 1) (p.val.1 0),p.val.2)=p.val
    rw [Function.update_eq_self,Prod.eta]
  · simp only [SpecialTransformations.Section5.FocusGeometry.eta,ite_eq_right hp]

theorem eta_identity_near_zero (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier A))
    (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D) :
    ∃ η : Gamma M,1 ≤ η ∧ ∀ p : A,η.val < vfValue (p.val.1 0) →
      ((SpecialTransformations.Section5.Primitive.centripetal D).toMap p).val=p.val := by
  obtain ⟨η,hη1,hInactive⟩ := inactive_near_zero D hc hs hsmall hA hD
  refine ⟨η,hη1,fun p hpSmall => ?_⟩
  by_cases hp0 : p.val.1 0=(0 : VF M)
  · exact eta_fixes_zero D p hp0
  · have hpNot := hInactive p hp0 hpSmall
    change D.toFocusGeometry.eta p.val=p.val
    simp only [SpecialTransformations.Section5.FocusGeometry.eta,ite_eq_right hpNot]

end DiamondIntegral.Section6.OriginalBaseOrdinaryFocus
