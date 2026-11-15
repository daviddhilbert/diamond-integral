import «section 5».FiniteValuePatterns

/-! Inverse comparison objects have genuine native finite value support,
including every zero-coordinate stratum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
local instance descendedFiniteStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem descendedOriginalSet_frameSupport {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (X : Set (Fin n → ℂ)) (hX : (Set.univ : Set ℂ).Definable Language.ring X) :
    HasFrameSupport N a (descendedOriginalSet N a X hX) := by
  intro r hr
  change r ∈ Set.range (fun u : descentSource N X hX => (descentMonomialMap N a X hX u).val) at hr
  rw [descentMonomialMap_range] at hr
  obtain ⟨root, x, hx, rfl⟩ := hr
  intro i
  change linePoint ((a i : ℚ) / (N : ℕ))
      (((root.val.2 ^ a i : ℂˣ) : ℂ) * x i) = none ∨
    value (linePoint ((a i : ℚ) / (N : ℕ))
      (((root.val.2 ^ a i : ℂˣ) : ℂ) * x i)) = _
  by_cases hc : (((root.val.2 ^ a i : ℂˣ) : ℂ) * x i) = 0
  · left
    exact dif_pos hc
  · right
    rw [linePoint, dif_neg hc]
    rfl

theorem finite_native_values_of_frameSupport {S : Set Carrier} {n : ℕ}
    (N : ℕ+) (a : Fin n → ℤ) (A : DefSet (rawRVSpace (M := Carrier) n) S)
    (hA : HasFrameSupport N a A) :
    (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite := by
  apply (native_finite_value_patterns_iff A).mpr
  have hp := Set.Finite.pi' (fun i : Fin n =>
    (Set.finite_singleton (((a i : ℚ) / (N : ℕ) : ℚ) : WithTop ℚ)).insert (⊤ : WithTop ℚ))
  apply hp.subset
  rintro p ⟨u, rfl⟩ i
  rcases hA u.val u.property i with h | h
  · simp [h, value]
  · exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr h)

theorem descendedOriginalSet_native_finite_values {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (X : Set (Fin n → ℂ)) (hX : (Set.univ : Set ℂ).Definable Language.ring X) :
    (Set.range (fun u : descendedOriginalSet N a X hX => fun i => Values.vrv (u.val i))).Finite :=
  finite_native_values_of_frameSupport N a _ (descendedOriginalSet_frameSupport N a X hX)

end DiamondIntegral.Section5.PuiseuxOriginal
