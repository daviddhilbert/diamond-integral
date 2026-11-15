import «section 5».ConstructibleFieldDefinability
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The actual Zariski topology on complex affine tuples, induced by
their evaluation-kernel points in the polynomial spectrum. Pure field
definable sets are constructible in this topology. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language Topology TopologicalSpace
open SpecialTransformations.Section7
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def complexZariskiTopology (n : ℕ) : TopologicalSpace (Fin n → ℂ) :=
  TopologicalSpace.induced (fieldTuplePrime (⊤ : Subfield ℂ)) inferInstance
attribute [local instance] complexZariskiTopology

theorem complexZariskiPoint_isInducing (n : ℕ) :
    IsInducing (fieldTuplePrime (⊤ : Subfield ℂ) : (Fin n → ℂ) → _) :=
  IsInducing.induced _

theorem complexZariskiPoint_injective (n : ℕ) :
    Function.Injective (fieldTuplePrime (⊤ : Subfield ℂ) : (Fin n → ℂ) → _) := by
  intro x y hxy
  funext i
  let p : MvPolynomial (Fin n) (⊤ : Subfield ℂ) := MvPolynomial.X i - MvPolynomial.C ⟨x i, by trivial⟩
  have hx : p ∈ (fieldTuplePrime (⊤ : Subfield ℂ) x).asIdeal := by
    simp [p, fieldTuplePrime, RingHom.mem_ker]
  rw [hxy] at hx
  have hy : y i - x i = 0 := by
    simpa [p, fieldTuplePrime, RingHom.mem_ker] using hx
  exact (sub_eq_zero.mp hy).symm

theorem complexZariskiPoint_isEmbedding (n : ℕ) :
    IsEmbedding (fieldTuplePrime (⊤ : Subfield ℂ) : (Fin n → ℂ) → _) :=
  ⟨complexZariskiPoint_isInducing n, complexZariskiPoint_injective n⟩

theorem complexZariski_noetherian (n : ℕ) : NoetherianSpace (Fin n → ℂ) :=
  (complexZariskiPoint_isInducing n).noetherianSpace
attribute [local instance] complexZariski_noetherian

theorem complex_definable_zariski_constructible {n : ℕ} (D : Set (Fin n → ℂ))
    (hD : (Set.univ : Set ℂ).Definable Language.ring D) : IsConstructible D := by
  obtain ⟨C, hC, he⟩ := field_definable_constructible (⊤ : Subfield ℂ) D hD
  have h := hC.preimage (complexZariskiPoint_isInducing n).continuous
    (fun _ _ _ => fun _ _ _ => NoetherianSpace.isCompact _)
  convert h using 1
  ext x
  exact he x

end DiamondIntegral.Section5
