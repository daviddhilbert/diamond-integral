import IntegrationSection5.RelativeLabelPreservation
import IntegrationSection5.HeadPreparation
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ} {H : DefSet (M := M) S (n+1) m} {K : DefSet (M := M) S (n+1) l}

theorem headSaturated_unary_fixed_image (f : Map H K) (hf : UnaryRelative f 0)
    (D : Set (Point (M := M) (n+1) m)) (hDH : D ⊆ carrier H) (hD : HeadSaturated D)
    (hVF : ∀ a : H, a.val ∈ D → vfAt (f a).val 0 = vfAt a.val 0)
    (hRV : ∀ a b : H, a.val ∈ D → b.val ∈ D → SameRV a.val b.val → SameRV (f a).val (f b).val) :
    HeadSaturated {q | ∃ a : H, a.val ∈ D ∧ (f a).val = q} := by
  rintro p ⟨a,ha,rfl⟩ x hx
  have hxA : rv x = rv (vfAt a.val 0) := hx.trans (congrArg rv (hVF a ha))
  have hbD : replace 0 a.val x ∈ D := hD a.val ha x hxA
  let b : H := ⟨replace 0 a.val x,hDH hbD⟩
  have hcell : SameRV a.val b.val := sameRV_replace 0 a.val x hxA
  have hr := ((sameRV_iff _ _).mp (hRV a b ha hbD hcell)).2
  refine ⟨b,hbD,?_⟩
  apply Prod.ext
  · funext j
    cases j using Fin.cases with
    | zero =>
      change vfAt (f b).val 0 = x
      exact (hVF b hbD).trans (by simp [b,replace,vfAt])
    | succ j =>
      have hja : j.succ ≠ (0 : Fin (n+1)) := Fin.succ_ne_zero j
      calc
        (f b).val.1 j.succ = b.val.1 j.succ := hf b j.succ hja
        _ = a.val.1 j.succ := by simp [b,replace,vfAt,Function.update_of_ne hja]
        _ = (f a).val.1 j.succ := (hf a j.succ hja).symm
        _ = (replace 0 (f a).val x).1 j.succ := by simp [replace,Function.update_of_ne hja]
  · exact hr.symm

end IntegrationInACVF.Section5
