import «section 3».FiniteFamilies
import Mathlib.Logic.Equiv.Set

/-! The underlying tagged carrier of a family product separates into
the two original tagged carriers, without selecting model elements. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
universe u v w x
def familySigmaProductEquiv {I : Type u} {J : Type v} (A : I → Type w) (B : J → Type x) :
    (Σ p : I × J, A p.1 × B p.2) ≃ (Σ i, A i) × (Σ j, B j) where
  toFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  invFun p := ⟨(p.1.1, p.2.1), (p.1.2, p.2.2)⟩
  left_inv p := by obtain ⟨⟨i, j⟩, a, b⟩ := p; rfl
  right_inv p := by obtain ⟨⟨i, a⟩, ⟨j, b⟩⟩ := p; rfl

end DiamondIntegral.Section3
