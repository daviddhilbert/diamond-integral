import «section 4».GammaPointAlgebra
import Mathlib.Algebra.Polynomial.Inductions

/-! The actual source polynomial ring Z[Gamma_def] + X FN[X]. Only
its constant coefficient must be a point function; all positive-degree
coefficients may be arbitrary original-base definable Euler functions. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section4.GammaFunctionPolynomial
open GammaDefinableConvolution GammaNamesSubgroup GammaPointAlgebra EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def sourceRing (B : GammaParameters.Base (M := M)) (k : EulerKind) :
    Subring (Polynomial (baseSubring B k)) := (pointSubring B k).comap Polynomial.constantCoeff

theorem mem_sourceRing (B : GammaParameters.Base (M := M)) (k : EulerKind)
    (p : Polynomial (baseSubring B k)) : p ∈ sourceRing B k ↔ p.coeff 0 ∈ pointSubring B k := Iff.rfl

theorem C_mem_sourceRing (B : GammaParameters.Base (M := M)) (k : EulerKind) (f : baseSubring B k) :
    Polynomial.C f ∈ sourceRing B k ↔ f ∈ pointSubring B k := by
  rw [mem_sourceRing, Polynomial.coeff_C_zero]

theorem monomial_mem_sourceRing (B : GammaParameters.Base (M := M)) (k : EulerKind)
    (n : ℕ) (hn : n ≠ 0) (f : baseSubring B k) : Polynomial.monomial n f ∈ sourceRing B k := by
  rw [mem_sourceRing, Polynomial.coeff_monomial, ite_eq_right hn]
  exact (pointSubring B k).zero_mem

theorem ray_C_not_mem_sourceRing (B : GammaParameters.Base (M := M)) (k : EulerKind)
    (a : additiveNames B) :
    Polynomial.C (⟨ray k a.val, ray_mem_base B k a.val a.property⟩ : baseSubring B k) ∉
      sourceRing B k := by
  intro h
  exact ray_not_mem_pointSubring B k a ((C_mem_sourceRing B k _).mp h)

theorem line_C_not_mem_sourceRing (B : GammaParameters.Base (M := M)) (k : EulerKind) :
    Polynomial.C (⟨line k, line_mem_base B k⟩ : baseSubring B k) ∉ sourceRing B k := by
  intro h
  exact line_not_mem_pointSubring B k ((C_mem_sourceRing B k _).mp h)

def assemble (B : GammaParameters.Base (M := M)) (k : EulerKind)
    (a : DefinableGammaGroupRing B) (p : Polynomial (baseSubring B k)) : sourceRing B k := by
  refine ⟨Polynomial.C (pointGroupRing B k a) + Polynomial.X * p, ?_⟩
  rw [mem_sourceRing, Polynomial.coeff_add, Polynomial.coeff_C_zero,
    Polynomial.coeff_X_mul_zero, add_zero]
  exact ⟨a, rfl⟩

theorem assemble_injective (B : GammaParameters.Base (M := M)) (k : EulerKind) :
    Function.Injective (fun z : DefinableGammaGroupRing B × Polynomial (baseSubring B k) =>
      assemble B k z.1 z.2) := by
  rintro ⟨a, p⟩ ⟨b, q⟩ h
  have he := congrArg Subtype.val h
  have h0 := congrArg (fun f : Polynomial (baseSubring B k) => f.coeff 0) he
  change (Polynomial.C (pointGroupRing B k a) + Polynomial.X * p).coeff 0 =
    (Polynomial.C (pointGroupRing B k b) + Polynomial.X * q).coeff 0 at h0
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_mul_zero,
    add_zero] at h0
  have hab : a = b := pointGroupRing_injective B k h0
  have hpq : p = q := by
    apply Polynomial.ext
    intro n
    have hn := congrArg (fun f : Polynomial (baseSubring B k) => f.coeff (n + 1)) he
    change (Polynomial.C (pointGroupRing B k a) + Polynomial.X * p).coeff (n + 1) =
      (Polynomial.C (pointGroupRing B k b) + Polynomial.X * q).coeff (n + 1) at hn
    simpa only [Polynomial.coeff_add, Polynomial.coeff_C_succ, Polynomial.coeff_X_mul,
      zero_add] using hn
  exact Prod.ext hab hpq

theorem assemble_surjective (B : GammaParameters.Base (M := M)) (k : EulerKind) :
    Function.Surjective (fun z : DefinableGammaGroupRing B × Polynomial (baseSubring B k) =>
      assemble B k z.1 z.2) := by
  intro p
  obtain ⟨a, ha⟩ := p.property
  refine ⟨⟨a, p.val.divX⟩, ?_⟩
  apply Subtype.ext
  change Polynomial.C (pointGroupRing B k a) + Polynomial.X * p.val.divX = p.val
  change pointGroupRing B k a = p.val.coeff 0 at ha
  rw [ha, add_comm]
  exact Polynomial.X_mul_divX_add p.val

def assemblyHom (B : GammaParameters.Base (M := M)) (k : EulerKind) :
    (DefinableGammaGroupRing B × Polynomial (baseSubring B k)) →+ sourceRing B k where
  toFun z := assemble B k z.1 z.2
  map_zero' := by
    apply Subtype.ext
    change Polynomial.C (pointGroupRing B k 0) + Polynomial.X * 0 = 0
    rw [(pointGroupRing B k).map_zero, Polynomial.C_0, mul_zero, add_zero]
  map_add' p q := by
    apply Subtype.ext
    change Polynomial.C (pointGroupRing B k (p.1 + q.1)) + Polynomial.X * (p.2 + q.2) =
      (Polynomial.C (pointGroupRing B k p.1) + Polynomial.X * p.2) +
        (Polynomial.C (pointGroupRing B k q.1) + Polynomial.X * q.2)
    rw [(pointGroupRing B k).map_add, Polynomial.C_add, mul_add]
    abel

def sourceDecomposition (B : GammaParameters.Base (M := M)) (k : EulerKind) :
    sourceRing B k ≃+ (DefinableGammaGroupRing B × Polynomial (baseSubring B k)) :=
  (AddEquiv.ofBijective (assemblyHom B k) ⟨assemble_injective B k, assemble_surjective B k⟩).symm

end DiamondIntegral.Section4.GammaFunctionPolynomial
