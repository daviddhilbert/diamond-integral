import «section 2».GammaPowerRadii

/-! The ordered-group calculation behind the unary Gamma case of 2.41:
finitely many rational-affine laws send a bounded interval to a bounded
interval. Signed slopes and empty domains are included. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gamma_symmetric_bound_iff (A : Set (Gamma M)) :
    (∃ γ : Gamma M, ∀ x ∈ A, γ⁻¹ ≤ x ∧ x ≤ γ) ↔ BddAbove A ∧ BddBelow A := by
  constructor
  · rintro ⟨γ,hγ⟩
    exact ⟨⟨γ,fun x hx => (hγ x hx).2⟩,γ⁻¹,fun x hx => (hγ x hx).1⟩
  · rintro ⟨⟨u,hu⟩,l,hl⟩
    refine ⟨max u l⁻¹,fun x hx => ⟨?_,(hu hx).trans (le_max_left _ _)⟩⟩
    have h : (max u l⁻¹)⁻¹ ≤ l := by
      simpa only [inv_inv] using (inv_le_inv' (le_max_right u l⁻¹))
    exact h.trans (hl hx)

theorem gamma_zpow_image_bounded (A : Set (Gamma M)) (hA : BddAbove A ∧ BddBelow A) (p : ℤ) :
    BddAbove ((fun x => x^p) '' A) ∧ BddBelow ((fun x => x^p) '' A) := by
  obtain ⟨u,hu⟩ := hA.1
  obtain ⟨l,hl⟩ := hA.2
  cases p with
  | ofNat n =>
    constructor
    · refine ⟨u^n,?_⟩
      rintro y ⟨x,hx,rfl⟩
      change x^(n : ℤ) ≤ u^n
      rw [zpow_natCast]
      exact pow_left_mono n (hu hx)
    · refine ⟨l^n,?_⟩
      rintro y ⟨x,hx,rfl⟩
      change l^n ≤ x^(n : ℤ)
      rw [zpow_natCast]
      exact pow_left_mono n (hl hx)
  | negSucc n =>
    constructor
    · refine ⟨(l^(n+1))⁻¹,?_⟩
      rintro y ⟨x,hx,rfl⟩
      simpa only [zpow_negSucc] using (inv_le_inv' (pow_left_mono (n+1) (hl hx)))
    · refine ⟨(u^(n+1))⁻¹,?_⟩
      rintro y ⟨x,hx,rfl⟩
      simpa only [zpow_negSucc] using (inv_le_inv' (pow_left_mono (n+1) (hu hx)))

def gammaPowerRelationImage (A : Set (Gamma M)) (p : ℤ) (q : ℕ) (c : Gamma M) : Set (Gamma M) :=
  {y | ∃ x ∈ A, y^q = c*x^p}

theorem gammaPowerRelationImage_bounded (A : Set (Gamma M)) (hA : BddAbove A ∧ BddBelow A)
    (p : ℤ) (q : ℕ) (hq : q ≠ 0) (c : Gamma M) :
    BddAbove (gammaPowerRelationImage A p q c) ∧ BddBelow (gammaPowerRelationImage A p q c) := by
  have hp := gamma_zpow_image_bounded A hA p
  obtain ⟨u,hu⟩ := hp.1
  obtain ⟨l,hl⟩ := hp.2
  let e := gammaPowerOrderIso (M := M) q hq
  constructor
  · refine ⟨e.symm (c*u),?_⟩
    rintro y ⟨x,hx,he⟩
    apply e.le_iff_le.mp
    rw [e.apply_symm_apply]
    change y^q ≤ c*u
    rw [he]
    exact (OrderIso.mulLeft c).monotone (hu (Set.mem_image_of_mem _ hx))
  · refine ⟨e.symm (c*l),?_⟩
    rintro y ⟨x,hx,he⟩
    apply e.le_iff_le.mp
    rw [e.apply_symm_apply]
    change c*l ≤ y^q
    rw [he]
    exact (OrderIso.mulLeft c).monotone (hl (Set.mem_image_of_mem _ hx))

theorem gamma_finite_power_laws_bounded {ι : Type} [Finite ι]
    (A : Set (Gamma M)) (hA : BddAbove A ∧ BddBelow A) (f : Gamma M → Gamma M)
    (p : ι → ℤ) (q : ι → ℕ) (hq : ∀ i, q i ≠ 0) (c : ι → Gamma M)
    (hcover : ∀ x ∈ A, ∃ i, f x ^ q i = c i * x ^ p i) :
    ∃ γ : Gamma M, ∀ y ∈ f '' A, γ⁻¹ ≤ y ∧ y ≤ γ := by
  classical
  have hi (i : ι) := gammaPowerRelationImage_bounded A hA (p i) (q i) (hq i) (c i)
  choose u hu using fun i => (hi i).1
  choose l hl using fun i => (hi i).2
  obtain ⟨U,hU⟩ := (Set.finite_range u).bddAbove
  obtain ⟨L,hL⟩ := (Set.finite_range l).bddBelow
  apply (gamma_symmetric_bound_iff (f '' A)).mpr
  constructor
  · refine ⟨U,?_⟩
    rintro y ⟨x,hx,rfl⟩
    obtain ⟨i,he⟩ := hcover x hx
    exact (hu i ⟨x,hx,he⟩).trans (hU (Set.mem_range_self i))
  · refine ⟨L,?_⟩
    rintro y ⟨x,hx,rfl⟩
    obtain ⟨i,he⟩ := hcover x hx
    exact (hL (Set.mem_range_self i)).trans (hl i ⟨x,hx,he⟩)

end DiamondIntegral.Section2
