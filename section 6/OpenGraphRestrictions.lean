import «section 6».PairedCoreRadiusIdentity

/-! Fixed-label VF charts, total derivatives and Jacobians survive a
literal restriction to open VF fibers. This is the analytic restriction
step for paired exceptional cores. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ}
variable {A C : Set (Mixed M n r)} {B D : Set (Mixed M n s)}

theorem mixed_chart_of_literal_open_restriction
    (f : A → B) (g : C → D) (hCA : C ⊆ A)
    (hpoint : ∀ q : C, (g q).val = (f ⟨q.val,hCA q.property⟩).val)
    (p : C) (F : (Fin n → VF M) → Fin n → VF M)
    (hNear : ∃ δ : Gamma M, ∀ x ∈ vfBall p.val.1 δ, (x,p.val.2) ∈ C)
    (hF : IsVFChartAt f ⟨p.val,hCA p.property⟩ F) : IsVFChartAt g p F := by
  obtain ⟨δ,hδ⟩ := hNear
  obtain ⟨ρ,hρ⟩ := hF
  refine ⟨max δ ρ,fun x hx => ?_⟩
  have hxC := hδ x (vfBall_anti (le_max_left _ _) hx)
  obtain ⟨hxA,hfx⟩ := hρ x (vfBall_anti (le_max_right _ _) hx)
  refine ⟨hxC,?_⟩
  rw [hpoint ⟨(x,p.val.2),hxC⟩]
  have hInput : (⟨(x,p.val.2),hCA hxC⟩ : A) = ⟨(x,p.val.2),hxA⟩ := Subtype.ext rfl
  rw [hInput,hfx]
  exact Prod.ext rfl (congrArg Prod.snd (hpoint p)).symm

theorem mixed_derivative_of_literal_open_restriction
    (f : A → B) (g : C → D) (hCA : C ⊆ A)
    (hpoint : ∀ q : C, (g q).val = (f ⟨q.val,hCA q.property⟩).val)
    (p : C) (L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M))
    (hNear : ∃ δ : Gamma M, ∀ x ∈ vfBall p.val.1 δ, (x,p.val.2) ∈ C)
    (hf : HasMixedVFDerivativeAt f ⟨p.val,hCA p.property⟩ L) : HasMixedVFDerivativeAt g p L := by
  obtain ⟨F,hF,hL⟩ := hf
  exact ⟨F,mixed_chart_of_literal_open_restriction f g hCA hpoint p F hNear hF,hL⟩

theorem mixed_jacobian_of_literal_open_restriction
    (f : A → B) (g : C → D) (hCA : C ⊆ A)
    (hpoint : ∀ q : C, (g q).val = (f ⟨q.val,hCA q.property⟩).val)
    (p : C) (J : VF M)
    (hNear : ∃ δ : Gamma M, ∀ x ∈ vfBall p.val.1 δ, (x,p.val.2) ∈ C)
    (hf : HasMixedVFJacobianAt f ⟨p.val,hCA p.property⟩ J) : HasMixedVFJacobianAt g p J := by
  obtain ⟨F,hF,hJ⟩ := hf
  exact ⟨F,mixed_chart_of_literal_open_restriction f g hCA hpoint p F hNear hF,hJ⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem open_fiber_contains_chart_ball
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C : Set (Mixed M n r)) (hC : ∀ u, IsOpen (vfFibre C u)) (p : C) :
    ∃ δ : Gamma M, ∀ x ∈ vfBall p.val.1 δ, (x,p.val.2) ∈ C :=
  exists_vfBall_subset_nhds hv p.val.1 ((hC p.val.2).mem_nhds p.property)

end DiamondIntegral.Section6
