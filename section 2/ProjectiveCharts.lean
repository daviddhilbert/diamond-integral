import «section 2».FiniteLimitMaps

/-!
# Coordinatewise reciprocal charts at projective boundary points

The prequel represents a projective coordinate by Option VF and specifies
its valuation neighbourhoods by memLimitBall. At an infinite coordinate
the reciprocal chart has centre zero and excludes zero from its domain.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

noncomputable def invertCoordinates (mask : Fin n → Bool) (x : Fin n → VF M) : Fin n → VF M :=
  fun i => if mask i then (x i)⁻¹ else x i

def inversionDomain (mask : Fin n → Bool) : Set (Fin n → VF M) :=
  {x | ∀ i, mask i = true → x i ≠ 0}

theorem invertCoordinates_involutive (mask : Fin n → Bool) :
    Function.Involutive (invertCoordinates (M := M) mask) := by
  intro x
  funext i
  cases h : mask i <;> simp only [invertCoordinates,h,Bool.false_eq_true,ite_false,ite_true,inv_inv]

theorem invertCoordinates_domain (mask : Fin n → Bool) (x : Fin n → VF M) :
    invertCoordinates mask x ∈ inversionDomain mask ↔ x ∈ inversionDomain mask := by
  apply forall_congr'
  intro i
  cases h : mask i <;> simp [inversionDomain,invertCoordinates,h]

def projectiveMask (b : Fin n → LimitPoint M) : Fin n → Bool := fun i => (b i).isNone

def projectiveCentre (b : Fin n → LimitPoint M) : Fin n → VF M := fun i => (b i).getD 0

def projectiveClosure (A : Set (Fin n → VF M)) (b : Fin n → LimitPoint M) : Prop :=
  ∀ ε : Gamma M, ∃ x ∈ A, ∀ i, memLimitBall (b i) ε (x i)

theorem vfValue_inv_finite (x : VF M) (hx : x ≠ 0) :
    vfValue x⁻¹ = ((finiteValue x hx)⁻¹).val := by
  change Values.vfValueHom x⁻¹ = ((finiteValue x hx)⁻¹).val
  rw [map_inv₀,Values.gamma_val_inv]
  rfl

theorem reciprocal_near_zero_iff (x : VF M) (hx : x ≠ 0) (ε : Gamma M) :
    ε.val < Values.vfValueHom x⁻¹ ↔ Values.vfValueHom x < (ε⁻¹).val := by
  have hval : Values.vfValueHom x = (finiteValue x hx).val := rfl
  rw [map_inv₀,hval,← Values.gamma_val_inv]
  change ε < (finiteValue x hx)⁻¹ ↔ finiteValue x hx < ε⁻¹
  constructor <;> intro h
  · simpa only [inv_inv] using inv_lt_inv' h
  · simpa only [inv_inv] using inv_lt_inv' h

theorem projectiveBall_in_domain (b : Fin n → LimitPoint M) (ε : Gamma M)
    (x : Fin n → VF M) (hx : ∀ i, memLimitBall (b i) ε (x i)) :
    x ∈ inversionDomain (projectiveMask b) := by
  intro i hi
  cases h : b i with
  | some a => simp only [projectiveMask,h,Option.isNone_some,Bool.false_eq_true] at hi
  | none =>
    intro hx0
    have hnear := hx i
    rw [h] at hnear
    change Values.vfValueHom (x i) < (ε⁻¹).val at hnear
    rw [hx0,map_zero,← Values.infinity_eq_zero] at hnear
    exact (not_lt_of_ge (Values.le_infinity _)) hnear

theorem projective_chart_near_iff (b : Fin n → LimitPoint M) (x : Fin n → VF M)
    (hx : x ∈ inversionDomain (projectiveMask b)) (ε : Gamma M) :
    invertCoordinates (projectiveMask b) x ∈ vfBall (projectiveCentre b) ε ↔
      ∀ i, memLimitBall (b i) ε (x i) := by
  apply forall_congr'
  intro i
  cases h : b i with
  | none =>
    have hx0 : x i ≠ 0 := hx i (by simp only [projectiveMask,h,Option.isNone_none])
    simpa only [invertCoordinates,projectiveMask,projectiveCentre,h,Option.isNone_none,
      Option.getD_none,ite_true,sub_zero,memLimitBall] using reciprocal_near_zero_iff (x i) hx0 ε
  | some a =>
    simp only [invertCoordinates,projectiveMask,projectiveCentre,h,Option.isNone_some,
      Bool.false_eq_true,ite_false,Option.getD_some,memLimitBall]

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuousAt_invertCoordinates (mask : Fin n → Bool) (x : Fin n → VF M)
    (hx : x ∈ inversionDomain mask) : ContinuousAt (invertCoordinates mask) x := by
  apply continuousAt_pi.mpr
  intro i
  cases h : mask i with
  | false =>
    simpa only [invertCoordinates,h,Bool.false_eq_true,ite_false] using
      (continuous_apply i).continuousAt
  | true =>
    have hp : ContinuousAt (fun z : Fin n → VF M => z i) x := (continuous_apply i).continuousAt
    have hi : ContinuousAt (Inv.inv : VF M → VF M) (x i) := continuousAt_inv₀ (hx i h)
    have hcomp : ContinuousAt (fun z : Fin n → VF M => (z i)⁻¹) x :=
      hi.comp (f := fun z : Fin n → VF M => z i) (x := x) hp
    simpa only [invertCoordinates,h,ite_true] using
      hcomp

theorem projectiveClosure_chart_mem_closure
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin n → VF M)) (b : Fin n → LimitPoint M) (hb : projectiveClosure A b) :
    projectiveCentre b ∈ closure
      (invertCoordinates (projectiveMask b) '' (A ∩ inversionDomain (projectiveMask b))) := by
  apply mem_closure_iff_nhds.mpr
  intro U hU
  obtain ⟨ε,hε⟩ := exists_vfBall_subset_nhds hv (projectiveCentre b) hU
  obtain ⟨x,hx,hnear⟩ := hb ε
  have hdom := projectiveBall_in_domain b ε x hnear
  have hchart := (projective_chart_near_iff b x hdom ε).mpr hnear
  exact ⟨invertCoordinates (projectiveMask b) x,hε hchart,x,⟨hx,hdom⟩,rfl⟩

/-- The projective neighbourhood definition restricts to ordinary affine
closure at every finite point. -/
theorem projectiveClosure_finite_iff
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin n → VF M)) (b : Fin n → VF M) :
    projectiveClosure A (finiteLimitPoint b) ↔ b ∈ closure A := by
  constructor
  · intro hb
    apply mem_closure_iff_nhds.mpr
    intro U hU
    obtain ⟨ε,hε⟩ := exists_vfBall_subset_nhds hv b hU
    obtain ⟨x,hx,hnear⟩ := hb ε
    exact ⟨x,hε hnear,hx⟩
  · intro hb ε
    obtain ⟨x,hxball,hx⟩ := (mem_closure_iff_nhds.mp hb) (vfBall b ε) (vfBall_mem_nhds hv b ε)
    exact ⟨x,hx,hxball⟩

end DiamondIntegral.Section2
