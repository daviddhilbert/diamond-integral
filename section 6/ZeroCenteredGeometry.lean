import «section 6».ZeroCenteredPreparation

/-! Exact bounds and local translation charts for zero-centered
preparation. Its derivative is the identity everywhere, including arity zero. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.ZeroCenteredData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem coordinate_value (D : ZeroCenteredData A) (p : Mixed M n r) (i : Fin n) :
    vfValue ((D.point p).1 i) = min (vfValue (p.1 i)) (vfValue D.center) := by
  classical
  by_cases hc : D.core p i = true
  · have hlt : vfValue D.center < vfValue (p.1 i) := of_decide_eq_true hc
    have he : rv M ((D.point p).1 i) = rv M D.center := by
      apply rv_eq_of_value_close D.center_nonzero
      simpa only [point,Pi.add_apply,shift,hc,ite_true,add_sub_cancel_right] using hlt
    exact (congrArg Values.vrv he).trans (min_eq_right hlt.le).symm
  · have hf := Bool.eq_false_iff.mpr hc
    have hle : vfValue (p.1 i) ≤ vfValue D.center := le_of_not_gt (of_decide_eq_false hf)
    simp only [point,Pi.add_apply,shift,hf,Bool.false_eq_true,ite_false,add_zero,min_eq_left hle]

theorem image_vfDoublyBounded (D : ZeroCenteredData A) : VFDoublyBounded D.map.image.carrier := by
  obtain ⟨γ,hγ⟩ := D.sourceProper.vfBounded
  let c := finiteValue D.center D.center_nonzero
  let δ : Gamma M := max γ⁻¹ (max c c⁻¹)
  have hlowγ : (δ⁻¹).val ≤ γ.val := show δ⁻¹ ≤ γ from by
    simpa only [inv_inv] using inv_le_inv' (show γ⁻¹ ≤ δ from le_max_left _ _)
  have hlowc : (δ⁻¹).val ≤ c.val := show δ⁻¹ ≤ c from by
    simpa only [inv_inv] using inv_le_inv' (show c⁻¹ ≤ δ from (le_max_right c c⁻¹).trans (le_max_right _ _))
  have hhighc : c.val ≤ δ.val := show c ≤ δ from (le_max_left c c⁻¹).trans (le_max_right _ _)
  rw [D.image_carrier]
  refine ⟨δ,?_⟩
  rintro _ ⟨p,hp,rfl⟩ i
  rw [D.coordinate_value]
  exact ⟨le_min (hlowγ.trans (hγ p hp i)) hlowc,(min_le_right _ _).trans hhighc⟩

theorem image_vfBounded (D : ZeroCenteredData A) : VFBounded D.map.image.carrier := by
  obtain ⟨γ,hγ⟩ := D.image_vfDoublyBounded
  exact ⟨γ⁻¹,fun p hp i => (hγ p hp i).1⟩

theorem image_rvDoublyBounded (D : ZeroCenteredData A) : RVSupportDoublyBounded D.map.image.carrier := by
  obtain ⟨γ,hγ⟩ := D.sourceProper.rvBounded
  let δ : Gamma M := max 1 γ
  have hlow : (δ⁻¹).val ≤ (γ⁻¹).val := show δ⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_right _ _)
  have hlow1 : (δ⁻¹).val ≤ (1 : GammaInfinity M) := show δ⁻¹ ≤ (1 : Gamma M) from by
    simpa only [inv_one] using inv_le_inv' (show (1 : Gamma M) ≤ δ from le_max_left _ _)
  have hhigh : γ.val ≤ δ.val := le_max_right _ _
  have hhigh1 : (1 : GammaInfinity M) ≤ δ.val := show (1 : Gamma M) ≤ δ from le_max_left _ _
  rw [D.image_carrier]
  refine ⟨δ,?_⟩
  rintro _ ⟨p,hp,rfl⟩ i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [point,tags,Fin.append_left,branchTag_value] using And.intro hlow1 hhigh1
  · simpa only [point,tags,Fin.append_right] using
      And.intro (hlow.trans (hγ p hp i).1) ((hγ p hp i).2.trans hhigh)

def branch (D : ZeroCenteredData A) (u : Fin r → RVInfinity M) (b : Fin n → Bool) :
    Set (Fin n → VF M) := {a | (a,u) ∈ A.carrier ∧ D.core (a,u) = b}

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem branch_isClopen (D : ZeroCenteredData A)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) (b : Fin n → Bool) : IsClopen (D.branch u b) := by
  have hcore (i : Fin n) : IsClopen {a : Fin n → VF M | D.core (a,u) i = true} := by
    have hp := (scalarBall_isClopen hv (finiteValue D.center D.center_nonzero)).preimage
      (show Continuous (fun a : Fin n → VF M => a i) from continuous_apply i)
    convert hp using 1
    ext a
    change (decide (vfValue D.center < vfValue (a i)) = true) ↔ vfValue D.center < vfValue (a i)
    simp only [decide_eq_true_eq]
  have htest (i : Fin n) : IsClopen {a : Fin n → VF M | D.core (a,u) i = b i} := by
    cases hb : b i
    · have he : {a : Fin n → VF M | D.core (a,u) i = false} =
          {a : Fin n → VF M | D.core (a,u) i = true}ᶜ := by
        ext a
        exact Bool.eq_false_iff
      rw [he]
      exact (hcore i).compl
    · exact hcore i
  have he : D.branch u b = vfFibre A.carrier u ∩ ⋂ i, {a | D.core (a,u) i = b i} := by
    ext a
    simp only [branch,Set.mem_inter_iff,Set.mem_iInter,Set.mem_setOf_eq,funext_iff]
    rfl
  rw [he]
  exact (D.sourceProper.clopen_fibres hv u).inter (isClopen_iInter_of_finite htest)

theorem point_on_branch (D : ZeroCenteredData A) (u : Fin r → RVInfinity M) (b : Fin n → Bool)
    {a : Fin n → VF M} (ha : a ∈ D.branch u b) : D.point (a,u) = (a + D.shift b,D.tags u b) := by
  simp only [point,ha.2]

theorem translation_chart (D : ZeroCenteredData A)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (p : A) :
    IsVFChartAt D.bijection p (fun x => x + D.shift (D.core p.val)) := by
  have hp : p.val.1 ∈ D.branch p.val.2 (D.core p.val) := ⟨p.property,rfl⟩
  obtain ⟨ρ,hρ⟩ := exists_vfBall_subset_nhds hv p.val.1
    ((D.branch_isClopen hv p.val.2 (D.core p.val)).isOpen.mem_nhds hp)
  refine ⟨ρ,fun x hx => ?_⟩
  have hxB := hρ hx
  refine ⟨hxB.1,?_⟩
  change D.point (x,p.val.2) = (_, (D.point p.val).2)
  rw [D.point_on_branch p.val.2 (D.core p.val) hxB]
  rfl

theorem unit_derivative (D : ZeroCenteredData A)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (p : A) :
    HasMixedUnitDerivativeAt D.bijection p := by
  obtain ⟨L,hL,hdet⟩ := hasUnitJacobianAt_translation (D.shift (D.core p.val)) p.val.1
  exact ⟨L,⟨_,D.translation_chart hv p,(hasDerivativeAt_iff_companion _ _ _).mp hL⟩,hdet⟩

end DiamondIntegral.Section6.ZeroCenteredData
