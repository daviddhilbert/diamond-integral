import «section 5».DiagonalConstructibleRing
import «section 5».EquivariantGraphDecomposition

/-! An actual constructible equivariant bijection, in sum coordinates,
with both uniqueness assertions and its exact source and target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language PuiseuxOriginal
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {n m : ℕ} {D : Set (Fin n → ℂ)} {E : Set (Fin m → ℂ)} (e : D ≃ E)

def complexEquivGraph : Set (Fin n ⊕ Fin m → ℂ) :=
  {z | ∃ x : D, (fun i => z (Sum.inl i)) = x.val ∧ (fun j => z (Sum.inr j)) = (e x).val}

theorem complexEquivGraph_pair (x : Fin n → ℂ) (y : Fin m → ℂ) :
    Sum.elim x y ∈ complexEquivGraph e ↔ ∃ u : D, x = u.val ∧ y = (e u).val := Iff.rfl

theorem sumTuple_comp_finSum (x : Fin n → ℂ) (y : Fin m → ℂ) :
    Sum.elim x y ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm = Fin.append x y := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem complexEquivGraph_definable
    (hG : (Set.univ : Set ℂ).Definable Language.ring (framedEquivGraph D E e)) :
    (Set.univ : Set ℂ).Definable Language.ring (complexEquivGraph e) := by
  have h := hG.preimage_comp (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm
  convert h using 1
  ext z
  simp [complexEquivGraph, framedEquivGraph, Function.comp_def]

theorem complexEquivGraph_forward_unique (x : Fin n → ℂ) (y z : Fin m → ℂ)
    (hy : Sum.elim x y ∈ complexEquivGraph e) (hz : Sum.elim x z ∈ complexEquivGraph e) : y = z := by
  obtain ⟨u, hxu, hyu⟩ := hy
  obtain ⟨v, hxv, hzv⟩ := hz
  have huv : u = v := Subtype.ext (hxu.symm.trans hxv)
  exact hyu.trans ((congrArg (fun w => (e w).val) huv).trans hzv.symm)

theorem complexEquivGraph_inverse_unique (y : Fin m → ℂ) (x z : Fin n → ℂ)
    (hx : Sum.elim x y ∈ complexEquivGraph e) (hz : Sum.elim z y ∈ complexEquivGraph e) : x = z := by
  obtain ⟨u, hxu, hyu⟩ := hx
  obtain ⟨v, hzv, hyv⟩ := hz
  have huv : u = v := e.injective (Subtype.ext (hyu.symm.trans hyv))
  exact hxu.trans ((congrArg Subtype.val huv).trans hzv.symm)

theorem complexEquivGraph_source (x : Fin n → ℂ) :
    (∃ y : Fin m → ℂ, Sum.elim x y ∈ complexEquivGraph e) ↔ x ∈ D := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨u, hxu, _⟩ := (complexEquivGraph_pair e x y).mp hy
    rw [hxu]
    exact u.property
  · intro hx
    exact ⟨(e ⟨x, hx⟩).val, ⟨x, hx⟩, rfl, rfl⟩

theorem complexEquivGraph_target (y : Fin m → ℂ) :
    (∃ x : Fin n → ℂ, Sum.elim x y ∈ complexEquivGraph e) ↔ y ∈ E := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨u, _, hyu⟩ := (complexEquivGraph_pair e x y).mp hx
    rw [hyu]
    exact (e u).property
  · intro hy
    refine ⟨(e.symm ⟨y, hy⟩).val, e.symm ⟨y, hy⟩, rfl, ?_⟩
    exact (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)).symm

theorem weightedAction_negative {r : ℕ} (a : Fin r → ℤ) (ζ : ℂˣ) (x : Fin r → ℂ) :
    weightedAction (fun i => -a i) ζ x = weightedAction a ζ⁻¹ x := by
  funext i
  simp [weightedAction, zpow_neg, inv_zpow]

theorem complexEquivGraph_finite_invariant (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (hG : FiniteInvariant N (Fin.append a b) (framedEquivGraph D E e)) :
    ∀ (ζ : rootsOfUnity (N : ℕ) ℂ) x y,
      Sum.elim (weightedAction (fun i => -a i) ζ.val x)
        (weightedAction (fun j => -b j) ζ.val y) ∈ complexEquivGraph e ↔
      Sum.elim x y ∈ complexEquivGraph e := by
  intro ζ x y
  have h := hG ζ⁻¹ (Fin.append x y)
  rw [weightedAction_append] at h
  simp only [framedEquivGraph, Set.mem_setOf_eq, Fin.append_left, Fin.append_right] at h
  simpa only [complexEquivGraph_pair, weightedAction_negative, Subgroup.coe_inv] using h

end DiamondIntegral.Section5
