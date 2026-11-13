import «section 3».GammaGroundRVGenericCoordinates
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Every coordinate row of an actual original-Gamma-ground RV set is
finite or cofinite in its value fibre. Auxiliary real codes are used only
to interpret the formula; no enlargement is asserted for the conclusion. -/
theorem gammaGroundRV_coordinate_row_finite_or_cofinite
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) {n : ℕ}
    (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A)
    (p : Fin n → M) (i : Fin n) (hp : NonzeroRV (p i)) :
    {x | SameScalar x (p i) ∧ Function.update p i x ∈ A}.Finite ∨
      {x | SameScalar x (p i) ∧ Function.update p i x ∉ A}.Finite := by
  let T : Set ((Fin n → M) × M) := {z | Function.update z.1 i z.2 ∈ A}
  let f : Fin n → Fin n ⊕ Fin 1 := fun j => if j = i then Sum.inr 0 else Sum.inl j
  have hT : RawClosure.Tuple.RelationDefinable (commonRealNames B) T := by
    change (commonRealNames B).Definable LRV
      {z : Fin n ⊕ Fin 1 → M | (z ∘ Sum.inl,z (Sum.inr 0)) ∈ T}
    convert hA.common_names.raw_definable.preimage_comp f using 1
    ext z
    change Function.update (z ∘ Sum.inl) i (z (Sum.inr 0)) ∈ A ↔ z ∘ f ∈ A
    have he : Function.update (z ∘ Sum.inl) i (z (Sum.inr 0)) = z ∘ f := by
      funext j
      by_cases hj : j = i <;> simp [f,hj]
    rw [he]
  have h := rawRVValuePart_finite_or_cofinite hc T hT (Fin.snoc p (p i)) (by simpa only [Fin.snoc_last] using hp)
  simpa only [rawRVValuePart,T,Set.mem_setOf_eq,Fin.snoc_last,Fin.init_snoc,
    ite_true,Bool.false_eq_true,ite_false] using h

end DiamondIntegral.Section3
