import «section 3».ACFIndependentFormulaTransport
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K] [CompatibleRing K] {n : ℕ}

/-- A definable partition of a residue torus has exactly one generic
branch. Only existence of one actual independent tuple is needed. -/
theorem acf_definable_partition_unique_generic {ι : Type}
    (E : Subfield K) (R : ι → Set (Fin n → K))
    (hR : ∀ i, (E : Set K).Definable Language.ring (R i))
    (hpart : ∀ x : Fin n → K, (∀ j, x j ≠ 0) → ∃! i, x ∈ R i)
    (x : Fin n → K) (hx : AlgebraicIndependent E x) :
    ∃! i, ∀ y : Fin n → K, AlgebraicIndependent E y → y ∈ R i := by
  obtain ⟨i,hi,hu⟩ := hpart x (algebraicallyIndependent_coordinate_ne_zero E x hx)
  refine ⟨i,?_,?_⟩
  · intro y hy
    exact (acf_independent_definable_iff E (R i) (hR i) x y hx hy).mp hi
  · intro j hj
    exact hu j (hj x hx)

end DiamondIntegral.Section3
