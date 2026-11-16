import «section 6».UnaryPullbackPreservation
import «section 6».ApertureCore

/-! The preliminary tagged zero-centered translation preserves an
RV-pullback ambient set, in every VF arity. True branches use source
invariance; false branches use the original RV-pullback property. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.ZeroCenteredData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem image_rvPullback (D : ZeroCenteredData A) (hA : IsRVPullback A.carrier) :
    IsRVPullback D.map.image.carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff D.map.image.carrier q).mp hq
  rw [D.image_carrier] at hp
  obtain ⟨a,ha,rfl⟩ := hp
  let b : Mixed M n r := (q.1-D.shift (D.core a),a.2)
  have hTrue (i : Fin n) (hi : D.core a i = true) : vfValue D.center < vfValue (b.1 i) := by
    have hai : vfValue D.center < vfValue (a.1 i) := of_decide_eq_true hi
    have hrva : rv M ((D.point a).1 i) = rv M D.center := by
      apply (rv_eq_iff_value_close D.center_nonzero).mpr
      simpa only [point,Pi.add_apply,shift,hi,ite_true,add_sub_cancel_right] using hai
    have hqrv : rv M (q.1 i) = rv M D.center := (congrFun hVF i).symm.trans hrva
    have hqnear := (rv_eq_iff_value_close D.center_nonzero).mp hqrv
    simpa only [b,Pi.sub_apply,shift,hi,ite_true] using hqnear
  have hFalse (i : Fin n) (hi : D.core a i = false) :
      rv M (b.1 i) = rv M (a.1 i) ∧ vfValue (b.1 i) ≤ vfValue D.center := by
    have hrv : rv M (q.1 i) = rv M (a.1 i) := by
      have h := (congrFun hVF i).symm
      simpa only [Section2.tupleRV,point,Pi.add_apply,shift,hi,Bool.false_eq_true,ite_false,add_zero] using h
    have hval : vfValue (q.1 i) = vfValue (a.1 i) := congrArg Values.vrv hrv
    have hai : vfValue (a.1 i) ≤ vfValue D.center := le_of_not_gt (of_decide_eq_false hi)
    simpa only [b,Pi.sub_apply,shift,hi,Bool.false_eq_true,ite_false,sub_zero] using
      And.intro hrv (hval.le.trans hai)
  have hbcore : D.core b = D.core a := by
    funext i
    cases hi : D.core a i
    · exact decide_eq_false (not_lt.mpr (hFalse i hi).2)
    · exact decide_eq_true (hTrue i hi)
  let z : Mixed M n r := (fun i => if D.core a i then a.1 i else b.1 i,a.2)
  have hz : z ∈ A.carrier := rvPullback_mem_of_sameRV hA ha (by
    funext i
    cases hi : D.core a i
    · simpa only [z,Section2.tupleRV,hi,Bool.false_eq_true,ite_false] using (hFalse i hi).1.symm
    · simp only [z,Section2.tupleRV,hi,ite_true]) rfl
  have hzb : Congruent (fun _ => finiteValue D.center D.center_nonzero) z.1 b.1 := by
    intro i
    change vfValue D.center < Values.vfValueHom (z.1 i-b.1 i)
    cases hi : D.core a i
    · simpa only [z,hi,Bool.false_eq_true,ite_false,sub_self,valueHom_eq_value,finiteValue] using
        gamma_lt_value_zero (finiteValue D.center D.center_nonzero)
    · have hai : vfValue D.center < vfValue (a.1 i) := of_decide_eq_true hi
      have hmin := vfValue_min_le_sub (a.1 i) (b.1 i)
      simpa only [z,hi,ite_true] using (lt_min hai (hTrue i hi)).trans_le hmin
  have hb : b ∈ A.carrier := (D.invariant a.2 z.1 b.1 hzb).mp hz
  rw [D.image_carrier]
  refine ⟨b,hb,Prod.ext ?_ ?_⟩
  · change b.1+D.shift (D.core b) = q.1
    rw [hbcore]
    exact sub_add_cancel _ _
  · change D.tags b.2 (D.core b) = q.2
    rw [hbcore,← hRV]
    rfl

end DiamondIntegral.Section6.ZeroCenteredData
