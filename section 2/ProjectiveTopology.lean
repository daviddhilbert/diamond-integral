import «section 2».ProjectiveLine
import «section 2».ProjectiveCharts
import «section 2».VFDefinableSets
import Mathlib.Topology.Constructions

/-!
# The released infinity-neighbourhood formulas and actual projective topology

Products of the two open affine charts give a neighbourhood basis.
Its intersection with finite VF tuples is exactly memLimitBall. Thus the
projectiveClosure predicate used by curve selection is actual closure in
the coordinatewise projective line with the valuation topology.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def finiteProjectiveTuple (x : Fin n → VF M) : Fin n → ProjectiveLine (VF M) :=
  fun i => ProjectiveLine.finite (x i)

def projectiveTuple (b : Fin n → LimitPoint M) : Fin n → ProjectiveLine (VF M) := fun i => ⟨b i⟩

noncomputable def projectiveTupleChart (b : Fin n → LimitPoint M)
    (x : Fin n → VF M) : Fin n → ProjectiveLine (VF M) :=
  fun i => match b i with
    | none => ProjectiveLine.reciprocalChart (x i)
    | some _ => ProjectiveLine.finite (x i)

def projectiveChartBall (b : Fin n → LimitPoint M) (ε : Gamma M) :
    Set (Fin n → ProjectiveLine (VF M)) :=
  projectiveTupleChart b '' vfBall (projectiveCentre b) ε

theorem projectiveTupleChart_centre (b : Fin n → LimitPoint M) :
    projectiveTupleChart b (projectiveCentre b) = projectiveTuple b := by
  classical
  funext i
  cases h : b i <;> simp [projectiveTupleChart,projectiveCentre,projectiveTuple,h,
    ProjectiveLine.reciprocalChart,ProjectiveLine.infinity,ProjectiveLine.finite]

theorem projectiveTupleChart_inverse (b : Fin n → LimitPoint M) (x : Fin n → VF M)
    (hx : x ∈ inversionDomain (projectiveMask b)) :
    projectiveTupleChart b (invertCoordinates (projectiveMask b) x) = finiteProjectiveTuple x := by
  classical
  funext i
  cases h : b i with
  | some a => simp [projectiveTupleChart,invertCoordinates,projectiveMask,finiteProjectiveTuple,h]
  | none =>
    have hx0 := hx i (by simp only [projectiveMask,h,Option.isNone_none])
    simp [projectiveTupleChart,invertCoordinates,projectiveMask,finiteProjectiveTuple,h,
      ProjectiveLine.reciprocalChart,hx0]

theorem projectiveTupleChart_eq_finite_iff (b : Fin n → LimitPoint M)
    (y x : Fin n → VF M) :
    projectiveTupleChart b y = finiteProjectiveTuple x ↔
      x ∈ inversionDomain (projectiveMask b) ∧ y = invertCoordinates (projectiveMask b) x := by
  classical
  constructor
  · intro he
    have hc (i : Fin n) : (projectiveMask b i = true → x i ≠ 0) ∧
        y i = invertCoordinates (projectiveMask b) x i := by
      have hi := congrFun he i
      cases h : b i with
      | some a =>
        have hyx : y i = x i := ProjectiveLine.finite_injective
          (by simpa only [projectiveTupleChart,finiteProjectiveTuple,h] using hi)
        exact ⟨by simp [projectiveMask,h],by
          simpa only [invertCoordinates,projectiveMask,h,Option.isNone_some,
            Bool.false_eq_true,ite_false] using hyx⟩
      | none =>
        have hi' : ProjectiveLine.reciprocalChart (y i) = ProjectiveLine.finite (x i) := by
          simpa only [projectiveTupleChart,finiteProjectiveTuple,h] using hi
        have hy0 : y i ≠ 0 := by
          intro hy0
          have hp := congrArg ProjectiveLine.point hi'
          simp [ProjectiveLine.reciprocalChart,hy0,ProjectiveLine.infinity,ProjectiveLine.finite] at hp
        have hix : (y i)⁻¹ = x i := ProjectiveLine.finite_injective
          (by simpa only [ProjectiveLine.reciprocalChart,ite_eq_right hy0] using hi')
        refine ⟨fun _ => ?_,?_⟩
        · rw [← hix]
          exact inv_ne_zero hy0
        · simp only [invertCoordinates,projectiveMask,h,Option.isNone_none,ite_true]
          rw [← hix,inv_inv]
    exact ⟨fun i => (hc i).1,funext (fun i => (hc i).2)⟩
  · rintro ⟨hx,rfl⟩
    exact projectiveTupleChart_inverse b x hx

theorem mem_projectiveChartBall_finite_iff (b : Fin n → LimitPoint M)
    (ε : Gamma M) (x : Fin n → VF M) :
    finiteProjectiveTuple x ∈ projectiveChartBall b ε ↔ ∀ i, memLimitBall (b i) ε (x i) := by
  constructor
  · rintro ⟨y,hy,he⟩
    obtain ⟨hx,rfl⟩ := (projectiveTupleChart_eq_finite_iff b y x).mp he
    exact (projective_chart_near_iff b x hx ε).mp hy
  · intro hnear
    have hx := projectiveBall_in_domain b ε x hnear
    exact ⟨invertCoordinates (projectiveMask b) x,(projective_chart_near_iff b x hx ε).mpr hnear,
      projectiveTupleChart_inverse b x hx⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem projectiveTupleChart_isOpenEmbedding (b : Fin n → LimitPoint M) :
    IsOpenEmbedding (projectiveTupleChart b) := by
  have h (i : Fin n) : IsOpenEmbedding (fun x : VF M => match b i with
      | none => ProjectiveLine.reciprocalChart x
      | some _ => ProjectiveLine.finite x) := by
    cases hi : b i with
    | none => simpa only [hi] using (ProjectiveLine.isOpenEmbedding_reciprocalChart (K := VF M))
    | some a => simpa only [hi] using (ProjectiveLine.isOpenEmbedding_finite (K := VF M))
  exact IsOpenEmbedding.piMap h

theorem projectiveChartBall_isOpen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (b : Fin n → LimitPoint M) (ε : Gamma M) : IsOpen (projectiveChartBall b ε) :=
  (projectiveTupleChart_isOpenEmbedding b).isOpenMap _ (vfBall_isOpen hv (projectiveCentre b) ε)

theorem projectiveChartBall_mem_nhds
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (b : Fin n → LimitPoint M) (ε : Gamma M) : projectiveChartBall b ε ∈ 𝓝 (projectiveTuple b) :=
  (projectiveChartBall_isOpen hv b ε).mem_nhds
    ⟨projectiveCentre b,mem_vfBall_self _ _,projectiveTupleChart_centre b⟩

theorem exists_projectiveChartBall_subset_nhds
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (b : Fin n → LimitPoint M) {W : Set (Fin n → ProjectiveLine (VF M))}
    (hW : W ∈ 𝓝 (projectiveTuple b)) : ∃ ε : Gamma M, projectiveChartBall b ε ⊆ W := by
  have hW' : W ∈ 𝓝 (projectiveTupleChart b (projectiveCentre b)) := by
    simpa only [projectiveTupleChart_centre] using hW
  have hcont : ContinuousAt (projectiveTupleChart b) (projectiveCentre b) :=
    (projectiveTupleChart_isOpenEmbedding b).continuous.continuousAt
  obtain ⟨ε,hε⟩ := exists_vfBall_subset_nhds hv (projectiveCentre b) (hcont.preimage_mem_nhds hW')
  exact ⟨ε,by rintro p ⟨x,hx,rfl⟩; exact hε hx⟩

theorem projectiveClosure_iff_topological
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin n → VF M)) (b : Fin n → LimitPoint M) :
    projectiveClosure A b ↔ projectiveTuple b ∈ closure (finiteProjectiveTuple '' A) := by
  constructor
  · intro hb
    apply mem_closure_iff_nhds.mpr
    intro W hW
    obtain ⟨ε,hε⟩ := exists_projectiveChartBall_subset_nhds hv b hW
    obtain ⟨x,hx,hnear⟩ := hb ε
    exact ⟨finiteProjectiveTuple x,hε ((mem_projectiveChartBall_finite_iff b ε x).mpr hnear),x,hx,rfl⟩
  · intro hb ε
    obtain ⟨p,hp,hpA⟩ := (mem_closure_iff_nhds.mp hb)
      (projectiveChartBall b ε) (projectiveChartBall_mem_nhds hv b ε)
    obtain ⟨x,hx,rfl⟩ := hpA
    exact ⟨x,hx,(mem_projectiveChartBall_finite_iff b ε x).mp hp⟩

end DiamondIntegral.Section2
