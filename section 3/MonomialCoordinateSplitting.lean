import «section 3».CoordinateProductChart
import «section 3».IntegerMonomialMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {n : ℕ} {Z : Set (Fin n)} {G : Type} [CommGroup G]

theorem coordinateProductChart_symm_zero (K : Section2.ZeroFaceChart Z)
    (r : Fin K.zeroArity → G) (u : Fin K.freeArity → G) (i : Fin K.zeroArity) :
    (coordinateProductChart K).symm (r,u) (K.zeroIndex i) = r i := by
  exact congrArg (fun p => p.1 i) ((coordinateProductChart K).apply_symm_apply (r,u))

theorem coordinateProductChart_symm_free (K : Section2.ZeroFaceChart Z)
    (r : Fin K.zeroArity → G) (u : Fin K.freeArity → G) (i : Fin K.freeArity) :
    (coordinateProductChart K).symm (r,u) (K.freeIndex i) = u i := by
  exact congrArg (fun p => p.2 i) ((coordinateProductChart K).apply_symm_apply (r,u))

/-- A row of the inverse monomial chart splits into a residue coefficient
and an integral monomial in the free coordinates. -/
theorem coordinateProductChart_character_split (K : Section2.ZeroFaceChart Z)
    (e : Fin n → ℤ) (r : Fin K.zeroArity → G) (u : Fin K.freeArity → G) :
    (∏ j, ((coordinateProductChart K).symm (r,u) j) ^ e j) =
      (∏ j, r j ^ e (K.zeroIndex j)) * (∏ j, u j ^ e (K.freeIndex j)) := by
  rw [← K.coordinates.prod_comp (fun j => ((coordinateProductChart K).symm (r,u) j) ^ e j)]
  rw [Fin.prod_univ_add]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro j _
    change ((coordinateProductChart K).symm (r,u) (K.zeroIndex j)) ^ e (K.zeroIndex j) = _
    rw [coordinateProductChart_symm_zero]
  · apply Finset.prod_congr rfl
    intro j _
    change ((coordinateProductChart K).symm (r,u) (K.freeIndex j)) ^ e (K.freeIndex j) = _
    rw [coordinateProductChart_symm_free]
end DiamondIntegral.Section3
