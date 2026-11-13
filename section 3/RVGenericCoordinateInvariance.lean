import «section 3».GammaGroundRVGenericCoordinates
import Section3.RVExchange
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

/-- Value equality in one coordinate, on complete nonzero RV tuples. -/
def RVCoordinateInvariant (A : Set (Fin n → M)) (i : Fin n) : Prop :=
  ∀ p : Fin n → M, (∀ j, NonzeroRV (p j)) → ∀ x : M, SameScalar x (p i) →
    (p ∈ A ↔ Function.update p i x ∈ A)

private theorem sameScalar_right {a b : M} (h : SameScalar a b) (x : M) :
    SameScalar x a ↔ SameScalar x b := by
  let c : Code (M := M) := ⟨⟨a,h.1.1⟩,h.1.2⟩
  let d : Code (M := M) := ⟨⟨b,h.2.1.1⟩,h.2.1.2⟩
  have hcd : value c = value d := (value_eq_iff c d).mpr ⟨h.2.2.1,h.2.2.2⟩
  exact (same_scalar_symm x a).trans ((same_scalar_code_left c d hcd x).trans (same_scalar_symm b x))

private theorem update_nonzero (p : Fin n → M) (hp : ∀ j, NonzeroRV (p j))
    (i : Fin n) (x : M) (hx : NonzeroRV x) : ∀ j, NonzeroRV (Function.update p i x j) := by
  intro j
  by_cases hj : j = i
  · subst j; simpa using hx
  · simpa [hj] using hp j

/-- One generic-coordinate operation already ignores the chosen
representative in that coordinate's entire value class. -/
theorem rvGenericCoordinate_invariant (A : Set (Fin n → M)) (i : Fin n) :
    RVCoordinateInvariant (rvGenericCoordinate A i) i := by
  intro p hp x hx
  have hq := update_nonzero p hp i x hx.1
  have hps : ∀ j, sortEval .rv (p j) := by intro j; simpa only [sortEval,iRV] using (hp j).1
  have hqs : ∀ j, sortEval .rv (Function.update p i x j) := by
    intro j; simpa only [sortEval,iRV] using (hq j).1
  rw [mem_rvGenericCoordinate_iff _ _ _ hps,mem_rvGenericCoordinate_iff _ _ _ hqs]
  simp only [Function.update_self]
  rw [and_iff_right (hp i),and_iff_right hx.1]
  have he : {z | SameScalar z (p i) ∧ Function.update p i z ∈ A} =
      {z | SameScalar z x ∧ Function.update (Function.update p i x) i z ∈ A} := by
    ext z
    simp only [Set.mem_setOf_eq,Function.update_idem]
    exact and_congr_left (fun _ => (sameScalar_right hx z).symm)
  rw [he]

/-- Generic selection in a different coordinate preserves every value
invariance already established. -/
theorem rvGenericCoordinate_preserves_invariant (A : Set (Fin n → M))
    (i j : Fin n) (hA : RVCoordinateInvariant A i) :
    RVCoordinateInvariant (rvGenericCoordinate A j) i := by
  by_cases hij : i = j
  · subst j
    exact rvGenericCoordinate_invariant A i
  intro p hp x hx
  have hq := update_nonzero p hp i x hx.1
  have hps : ∀ k, sortEval .rv (p k) := by intro k; simpa only [sortEval,iRV] using (hp k).1
  have hqs : ∀ k, sortEval .rv (Function.update p i x k) := by
    intro k; simpa only [sortEval,iRV] using (hq k).1
  rw [mem_rvGenericCoordinate_iff _ _ _ hps,mem_rvGenericCoordinate_iff _ _ _ hqs]
  have hji : j ≠ i := Ne.symm hij
  simp only [Function.update_of_ne hji]
  apply and_congr_right
  intro hj
  have he : {z | SameScalar z (p j) ∧ Function.update p j z ∈ A} =
      {z | SameScalar z (p j) ∧ Function.update (Function.update p i x) j z ∈ A} := by
    ext z
    simp only [Set.mem_setOf_eq]
    apply and_congr_right
    intro hz
    have hpz := update_nonzero p hp j z hz.1
    have hxi : SameScalar x (Function.update p j z i) := by simpa [hij] using hx
    have h := hA (Function.update p j z) hpz x hxi
    rw [← Function.update_comm hij x z p] at h
    exact h
  rw [he]

/-- Any finite iteration retains all earlier coordinate invariances. -/
theorem rvGenericCoordinate_fold_preserves_invariant (A : Set (Fin n → M))
    (L : List (Fin n)) (i : Fin n) (hA : RVCoordinateInvariant A i) :
    RVCoordinateInvariant (L.foldl rvGenericCoordinate A) i := by
  induction L generalizing A with
  | nil => exact hA
  | cons j L ih => exact ih _ (rvGenericCoordinate_preserves_invariant A i j hA)

theorem rvGenericCoordinate_fold_invariant (A : Set (Fin n → M))
    (L : List (Fin n)) (i : Fin n) (hi : i ∈ L) :
    RVCoordinateInvariant (L.foldl rvGenericCoordinate A) i := by
  induction L generalizing A with
  | nil => simp at hi
  | cons j L ih =>
    rcases List.mem_cons.mp hi with h | h
    · subst j
      exact rvGenericCoordinate_fold_preserves_invariant _ L i (rvGenericCoordinate_invariant A i)
    · exact ih _ h

end DiamondIntegral.Section3
