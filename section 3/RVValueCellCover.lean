import «section 3».RVClauseCharacters
import Mathlib.Data.Fintype.Pi
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def literalValueMask (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) : Bool :=
  match L with
  | .equality E _ => decide (RVOperations.absoluteHom (E.left.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))) =
      RVOperations.absoluteHom (E.right.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))))
  | .order _ _ => false

theorem literalValueCell_own_mask (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) : literalValueCell L a r (literalValueMask L a r x) x := by
  cases L <;> simp only [literalValueCell,literalValueMask,decide_eq_true_eq,iff_self]

theorem rvClauseValueCells_cover (C : Finset (RVLiteral I R (Fin n)))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    (∀ L ∈ C, RVLiteral.comparison a r (fun i => (x i : CanonicalRV.RVSort M)) L) ↔
      ∃ b : C → Bool, x ∈ rvClauseValueCell C a r b := by
  constructor
  · intro hx
    exact ⟨fun L => literalValueMask L.val a r x,hx,fun L => literalValueCell_own_mask L.val a r x⟩
  · rintro ⟨b,hx⟩
    exact hx.1

theorem rvClauseValueCells_finite (C : Finset (RVLiteral I R (Fin n)))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) :
    (Set.range (rvClauseValueCell C a r)).Finite := Set.finite_range _
end DiamondIntegral.Section3
