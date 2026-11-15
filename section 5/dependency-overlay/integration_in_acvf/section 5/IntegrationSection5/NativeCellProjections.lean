import IntegrationSection5.MixedUnaryPreparations
import IntegrationSection5.CellLabelInjection

/-! Native-order cell fibres and the actual mixed unary projections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {m : ℕ}

theorem unaryPoint_eta (p : Point (M := M) 1 m) : (fun _ : Fin 1 => vfAt p 0,p.2) = p := by
  apply Prod.ext
  · funext j; fin_cases j; rfl
  · rfl

theorem nativePairPoint_eta (p : Point (M := M) 2 m) : (![vfAt p 0,vfAt p 1],p.2) = p := by
  apply Prod.ext
  · funext j; fin_cases j <;> rfl
  · rfl

theorem mixed_first_projection_fibre_iff (A : Set (Point (M := M) 2 m)) (p : Point (M := M) 1 m) :
    p ∈ mixedUnaryProjectionSet A 0 ↔ vfAt p 0 ∈ Cells.first (nativeTwoFibre A p.2) := by
  constructor
  · rintro ⟨q,hq,hqp⟩
    have hl : q.2 = p.2 := congrArg (fun z : Point (M := M) 1 m => z.2) hqp
    have hx : vfAt q 0 = vfAt p 0 := congrArg (fun z : Point (M := M) 1 m => vfAt z 0) hqp
    refine ⟨(vfAt q 0,vfAt q 1),?_,hx⟩
    change (![vfAt q 0,vfAt q 1],p.2) ∈ A
    rw [← hl,nativePairPoint_eta]
    exact hq
  · rintro ⟨q,hq,hqp⟩
    let z : Point (M := M) 2 m := (![q.1,q.2],p.2)
    refine ⟨z,hq,?_⟩
    apply Prod.ext
    · funext j; fin_cases j; exact hqp
    · rfl

theorem mixed_second_projection_fibre_iff (A : Set (Point (M := M) 2 m)) (p : Point (M := M) 1 m) :
    p ∈ mixedUnaryProjectionSet A 1 ↔ vfAt p 0 ∈ Cells.second (nativeTwoFibre A p.2) := by
  constructor
  · rintro ⟨q,hq,hqp⟩
    have hl : q.2 = p.2 := congrArg (fun z : Point (M := M) 1 m => z.2) hqp
    have hx : vfAt q 1 = vfAt p 0 := congrArg (fun z : Point (M := M) 1 m => vfAt z 0) hqp
    refine ⟨(vfAt q 0,vfAt q 1),?_,hx⟩
    change (![vfAt q 0,vfAt q 1],p.2) ∈ A
    rw [← hl,nativePairPoint_eta]
    exact hq
  · rintro ⟨q,hq,hqp⟩
    let z : Point (M := M) 2 m := (![q.1,q.2],p.2)
    refine ⟨z,hq,?_⟩
    apply Prod.ext
    · funext j; fin_cases j; exact hqp
    · rfl

end IntegrationInACVF.Section5
