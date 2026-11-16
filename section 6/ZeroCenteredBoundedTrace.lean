import «section 6».UnaryPullbackPreservation
import «section 6».ZeroCenteredGeometry

/-! A zero-centred preliminary operation has no active coordinates on
an already doubly bounded source. This follows from its actual source
invariance: an active coordinate would force a zero coordinate into the
source. Its remaining action only appends constant branch labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.ZeroCenteredData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem core_false_of_doublyBounded (D : ZeroCenteredData A)
    (hA : VFDoublyBounded A.carrier) {p : Mixed M n r} (hp : p ∈ A.carrier) (i : Fin n) :
    D.core p i = false := by
  apply Bool.eq_false_iff.mpr
  intro hCore
  have hlt : vfValue D.center < vfValue (p.1 i) := of_decide_eq_true hCore
  let x := Function.update p.1 i 0
  have hClose : Congruent (fun _ => finiteValue D.center D.center_nonzero) p.1 x := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [x,Function.update_self,sub_zero,finiteValue] using hlt
    · simpa only [x,Function.update_of_ne hj,sub_self,valueHom_eq_value] using
        gamma_lt_value_zero (finiteValue D.center D.center_nonzero)
  have hx : (x,p.2) ∈ A.carrier := (D.invariant p.2 p.1 x hClose).mp hp
  exact hA.nonzero hx i (Function.update_self _ _ _)

theorem point_field_of_doublyBounded (D : ZeroCenteredData A)
    (hA : VFDoublyBounded A.carrier) {p : Mixed M n r} (hp : p ∈ A.carrier) :
    (D.point p).1 = p.1 := by
  funext i
  simp only [point,Pi.add_apply,shift,D.core_false_of_doublyBounded hA hp i,
    Bool.false_eq_true,ite_false,add_zero]

theorem point_tags_of_doublyBounded (D : ZeroCenteredData A)
    (hA : VFDoublyBounded A.carrier) {p : Mixed M n r} (hp : p ∈ A.carrier) :
    (D.point p).2 = Fin.append (fun _ : Fin n => branchTag (M := M) false) p.2 := by
  change Fin.append (fun i => branchTag (M := M) (D.core p i)) p.2 = _
  congr 1
  funext i
  rw [D.core_false_of_doublyBounded hA hp i]

theorem image_rvPullback_of_doublyBounded (D : ZeroCenteredData A)
    (hA : VFDoublyBounded A.carrier) (hRP : IsRVPullback A.carrier) :
    IsRVPullback D.map.image.carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff D.map.image.carrier q).mp hq
  rw [D.image_carrier] at hp ⊢
  obtain ⟨a,ha,rfl⟩ := hp
  let b : Mixed M n r := (q.1,a.2)
  have hb : b ∈ A.carrier := rvPullback_mem_of_sameRV hRP ha (by
    rw [D.point_field_of_doublyBounded hA ha] at hVF
    exact hVF) rfl
  refine ⟨b,hb,Prod.ext (D.point_field_of_doublyBounded hA hb) ?_⟩
  rw [D.point_tags_of_doublyBounded hA hb,← hRV,D.point_tags_of_doublyBounded hA ha]

end DiamondIntegral.Section6.ZeroCenteredData
