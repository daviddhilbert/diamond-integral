import «section 2».ProjectiveTopology
import Mathlib.Topology.Separation.Hausdorff

/-! Finite VF tuples are dense in the two-chart projective product.
The released finite/infinity ball separation therefore proves actual
Hausdorff separation, without a local compactness assumption. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem projectiveClosure_univ (b : Fin n → LimitPoint M) :
    projectiveClosure Set.univ b := by
  intro ε
  obtain ⟨γ,hγ⟩ := exists_lt ε⁻¹
  obtain ⟨r,hr,hval⟩ := gamma_has_vf_representative γ
  let x : Fin n → VF M := fun i => (b i).getD r
  refine ⟨x,Set.mem_univ _,?_⟩
  intro i
  cases hi : b i with
  | none =>
    have hsmall : Values.vfValueHom r < (ε⁻¹).val := by rw [hval]; exact hγ
    simpa only [x,hi,Option.getD_none,memLimitBall] using hsmall
  | some a =>
    simpa only [x,hi,Option.getD_some,memLimitBall,sub_self] using gamma_lt_value_zero ε

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem finiteProjectiveTuple_denseRange
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (n : ℕ) :
    DenseRange (finiteProjectiveTuple (M := M) (n := n)) := by
  intro p
  let b : Fin n → LimitPoint M := fun i => (p i).point
  have hp : projectiveTuple b = p := rfl
  have h := (projectiveClosure_iff_topological hv Set.univ b).mp (projectiveClosure_univ b)
  rw [hp,Set.image_univ] at h
  exact h

theorem projectiveProduct_t2Space
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (n : ℕ) :
    T2Space (Fin n → ProjectiveLine (VF M)) := by
  constructor
  intro p q hpq
  let b : Fin n → LimitPoint M := fun i => (p i).point
  let c : Fin n → LimitPoint M := fun i => (q i).point
  have hbc : b ≠ c := by
    intro he
    apply hpq
    change projectiveTuple b = projectiveTuple c
    rw [he]
  obtain ⟨ε,hε⟩ := exists_disjoint_limitBall hbc
  have hU := projectiveChartBall_isOpen hv b ε
  have hV := projectiveChartBall_isOpen hv c ε
  refine ⟨projectiveChartBall b ε,projectiveChartBall c ε,hU,hV,
    ⟨projectiveCentre b,mem_vfBall_self _ _,projectiveTupleChart_centre b⟩,
    ⟨projectiveCentre c,mem_vfBall_self _ _,projectiveTupleChart_centre c⟩,?_⟩
  apply Set.disjoint_left.mpr
  intro z hzU hzV
  obtain ⟨w,⟨x,rfl⟩,hx⟩ := Dense.exists_mem_open (finiteProjectiveTuple_denseRange hv n)
    (hU.inter hV) ⟨z,hzU,hzV⟩
  exact Set.disjoint_left.mp hε
    ((mem_projectiveChartBall_finite_iff b ε x).mp hx.1)
    ((mem_projectiveChartBall_finite_iff c ε x).mp hx.2)

end DiamondIntegral.Section2
