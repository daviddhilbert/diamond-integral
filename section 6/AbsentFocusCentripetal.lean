import «section 6».CentripetalCoreMembership
import «section 6».UnaryCentripetalExistence

/-! If the actual focus graph misses the current source, a permitted
finite-aperture component has no contracted core there. It agrees with
the ordinary translation at every point, with one retained false tag. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalData.core_false_of_focus_absent
    {A : DefSet (rawMixedSpace (M := M) n r) S} (D : CentripetalData (G := G) A)
    (p : Mixed M n r) (hp : p ∈ A.carrier)
    (hAbsent : p.2 ∈ D.activeTags.carrier → D.focusPoint p ∉ A.carrier) : D.core p=false := by
  by_cases hu : p.2 ∈ D.activeTags.carrier
  · apply decide_eq_false
    intro hCore
    rw [D.extendedFocus_active hp hu] at hCore
    exact hAbsent hu ((D.core_membership_iff_focus p hu hCore).mp hp)
  · exact D.core_inactive hu

theorem CentripetalData.point_eq_translation_of_focus_absent
    {A : DefSet (rawMixedSpace (M := M) n r) S} (D : CentripetalData (G := G) A)
    (p : Mixed M n r) (hp : p ∈ A.carrier)
    (hAbsent : p.2 ∈ D.activeTags.carrier → D.focusPoint p ∉ A.carrier) :
    D.point p=(Function.update p.1 D.coordinate (p.1 D.coordinate-D.extendedFocus p),
      Fin.append (fun _ : Fin 1 => branchTag false) p.2) := by
  simp only [CentripetalData.point,D.core_false_of_focus_absent p hp hAbsent,Bool.false_eq_true,
    if_false,add_zero]

theorem UnaryFocusData.exists_centripetal_without_core
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} (D : UnaryFocusData A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hAbsent : ∀ p ∈ A.carrier,p.2 ∈ D.activeTags.carrier →
      ((fun _ : Fin 1 => D.focus p.2),p.2) ∉ A.carrier) :
    ∃ E : CentripetalData (G := G) A,E.coordinate=0 ∧ E.activeTags=D.activeTags ∧
      (∀ x u,E.focus x u=D.focus u) ∧ ∀ p ∈ A.carrier,E.core p=false := by
  obtain ⟨E,hCoord,hActive,hFocus,hMap⟩ := D.exists_centripetal_data h00 hc linear hκ hs hv
    V hsmall hΓ hV hVS hSV hnt
  refine ⟨E,hCoord,hActive,hFocus,fun p hp => E.core_false_of_focus_absent p hp ?_⟩
  intro hu
  have hEq : E.focusPoint p=((fun _ : Fin 1 => D.focus p.2),p.2) := by
    apply Prod.ext
    · funext i
      fin_cases i
      simp only [CentripetalData.focusPoint,hCoord,hFocus]
      change Function.update p.1 (0 : Fin 1) (D.focus p.2) (0 : Fin 1)=D.focus p.2
      exact Function.update_self _ _ _
    · rfl
  rw [hEq]
  exact hAbsent p hp (hActive ▸ hu)

end DiamondIntegral.Section6
