import «section 5».GammaCellSyntaxValidity
import Section4.CanonicalNormalization

/-! Parameter-free original-language formulas for native Gamma code
properness, equality and strict order. No residue or value code is named. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure NativeGammaRelationSyntax (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] where
  proper : LRV.Formula (Fin 1)
  equal : LRV.Formula (Fin 2)
  less : LRV.Formula (Fin 2)
  proper_realize : ∀ t : Fin 1 → M, proper.Realize t ↔ NonzeroRV (t 0)
  equal_realize : ∀ x y : M, NonzeroRV x → NonzeroRV y →
    (equal.Realize ![x, y] ↔ codeValue x = codeValue y)
  less_realize : ∀ x y : M, NonzeroRV x → NonzeroRV y →
    (less.Realize ![x, y] ↔ codeValue x < codeValue y)

theorem native_gamma_relation_syntax_exists (hc : CanonicalStructure.IsCanonical (M := M)) :
    Nonempty (NativeGammaRelationSyntax M) := by
  obtain ⟨U, hU⟩ := Set.empty_definable_iff.mp (nonzero_rv_definable (M := M) ∅)
  obtain ⟨E, hE⟩ := Set.empty_definable_iff.mp (same_scalar_definable (M := M) ∅)
  have hlt := EndpointLogic.codeLt_definable (M := M) ∅
  rw [canonical_normalize_eq hc] at hlt
  obtain ⟨T, hT⟩ := Set.empty_definable_iff.mp hlt
  refine ⟨⟨U, E, T, ?_, ?_, ?_⟩⟩
  · intro t
    exact (Set.ext_iff.mp hU t).symm
  · intro x y hx hy
    have he : E.Realize ![x, y] ↔ SameScalar x y := (Set.ext_iff.mp hE ![x, y]).symm
    rw [he]
    constructor
    · intro h
      exact le_antisymm ((original_le_codeValue_iff x y hx hy).mp h.2.2.1)
        ((original_le_codeValue_iff y x hy hx).mp h.2.2.2)
    · intro h
      exact ⟨hx, hy, (original_le_codeValue_iff x y hx hy).mpr (le_of_eq h),
        (original_le_codeValue_iff y x hy hx).mpr (le_of_eq h.symm)⟩
  · intro x y hx hy
    exact ((Set.ext_iff.mp hT ![x, y]).symm).trans (EndpointLogic.codeLt_iff x y hx hy)

def nativeGammaRelationSyntax (hc : CanonicalStructure.IsCanonical (M := M)) : NativeGammaRelationSyntax M :=
  Classical.choice (native_gamma_relation_syntax_exists hc)

end DiamondIntegral.Section5
