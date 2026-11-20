import «section 7».BlowupResults
import «section 7».FiberwiseInput
import «section 4».RelativeAnnularGenerators

/-! Classes of `μRV^db[k]` in the graded ring `K μRV^db[*]`, and `μIsp^db`
modulo `J_var` (for Remark 7.25 and Theorem 7.26).

`clsRing : Cls B k →+ K μRV^db[*]` sends the class of a bounded object to its
class in Section 4's ring presentation (`RVBoundedRing.objectClass`). A blowup
step replaces sources `[U_i]` by elementary blowups `[U_i^{τ,j}]`, so it changes
`clsRing` by a sum of the manuscript generators `[U^{τ,j}] − [U]` of `J_var`
(`step_mem`). Hence `μIsp^db`-related classes differ by an element of `J_var`
(`muIsp_mem`, `ispRel_mem`): the first half of Remark 7.25 on the RV side. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.RingClasses
open DiamondIntegral.Section4 DiamondIntegral.Section4.RelativeAnnularGenerators DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.FiberwiseInput

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

/-- **The class in the graded ring** `K μRV^db[*]` (Section 4's presentation). -/
def clsRing : Cls B k →+ RVBoundedRing.Ring B where
  toFun := Quotient.lift (fun a : Obj B k => RVBoundedRing.objectClass a)
    (fun _ _ h => by
      obtain ⟨F⟩ := h
      exact RVBoundedRing.objectClass_iso F)
  map_zero' := RVBoundedRing.objectClass_empty (emptyObj B k) (Set.eq_empty_of_forall_notMem fun _ h => h.elim)
  map_add' x y := Quotient.inductionOn₂ x y fun a b =>
    RVTaggedCoproductClasses.bounded_coproduct_class a b

theorem clsRing_cls (a : Obj B k) : clsRing (cls a) = RVBoundedRing.objectClass a := rfl

/-- A blowup step changes the ring class by an element of `J_var`. -/
theorem step_mem {x y : Cls B (1 + k)} (h : Step x y) : clsRing y - clsRing x ∈ manuscriptIdeal B := by
  obtain ⟨n, D, z, rfl, rfl⟩ := h
  rw [map_add, map_add, map_sum, map_sum, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  exact Ideal.subset_span ⟨k, D i, rfl⟩

theorem steps_mem {n : ℕ} {x y : Cls B (1 + k)} (h : BlowupSteps n x y) :
    clsRing y - clsRing x ∈ manuscriptIdeal B := by
  induction h with
  | refl _ => rw [sub_self]; exact Ideal.zero_mem _
  | cons hab _ ih =>
    have := Ideal.add_mem _ ih (step_mem hab)
    rwa [sub_add_sub_cancel] at this

/-- **`μIsp^db`-related classes differ by an element of `J_var`.** -/
theorem muIsp_mem {x y : Cls B (1 + k)} (h : MuIsp x y) : clsRing x - clsRing y ∈ manuscriptIdeal B := by
  obtain ⟨w, m, n, hx, hy⟩ := h
  have h1 := steps_mem hx
  have h2 := steps_mem hy
  have := Ideal.sub_mem _ h2 h1
  rwa [sub_sub_sub_cancel_left] at this

theorem clsRing_cast {a b : ℕ} (h : a = b) (x : Cls B a) : clsRing (castCls h x) = clsRing x := by
  subst h
  rfl

/-- The same in degree `n + 1`, for the relation `IspRel`. -/
theorem ispRel_mem {n : ℕ} {x y : Cls B (n + 1)} (h : IspRel x y) : clsRing x - clsRing y ∈ manuscriptIdeal B := by
  rw [ispRel_iff (show n + 1 = 1 + n by omega)] at h
  have := muIsp_mem h
  rwa [clsRing_cast, clsRing_cast] at this

end DiamondIntegral.Section7.RingClasses
