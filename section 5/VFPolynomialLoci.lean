import «section 5».NativeGammaPointBridge
import Section5.PolynomialPreparation
import Section4.CanonicalNormalization

/-! Actual finite polynomial equation loci over named VF coefficients
are original-ground definable, with no RV coordinate or parameter added. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open DiamondIntegral.Section3 SpecialTransformations.ModelTheory
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

def vfPolynomialRawCode (p : MvPolynomial (Fin n) (VFType (M := M))) (z : Fin n → M) : M :=
  mvPolynomialCode (m := 0) p (Sum.elim z Fin.elim0)

theorem vfPolynomialRawCode_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (p : MvPolynomial (Fin n) (VFType (M := M)))
    (hcoeff : ∀ d,(p.coeff d).val ∈ B.real) :
    B.real.DefinableFun LRV (vfPolynomialRawCode p) := by
  have hp := mvPolynomialCode_definable (m := 0) p hcoeff
  change @Set.DefinableFun M LRV (CanonicalStructure.normalize (M := M)) (Fin n ⊕ Fin 0) B.real (mvPolynomialCode (m := 0) p) at hp
  rw [canonical_normalize_eq hc] at hp
  change B.real.DefinableFun LRV (fun z : Fin n → M => mvPolynomialCode (m := 0) p (Sum.elim z Fin.elim0))
  exact hp.comp (g := fun z : Fin n → M => Sum.elim z (Fin.elim0 : Fin 0 → M))
    (show B.real.DefinableMap LRV (fun z : Fin n → M => Sum.elim z (Fin.elim0 : Fin 0 → M)) from by
      intro i
      cases i with
      | inl j => exact Set.DefinableFun.proj LRV
      | inr j => exact j.elim0)

theorem vfPolynomial_zero_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (p : MvPolynomial (Fin n) (VFType (M := M)))
    (hcoeff : ∀ d,(p.coeff d).val ∈ B.real) :
    DefinableOverBase B (fun _ : Fin n => .vf)
      {z | z ∈ sortedUniverse (fun _ : Fin n => .vf) ∧ vfPolynomialRawCode p z = iVFZero} := by
  have hp := vfPolynomialRawCode_definable hc p hcoeff
  have h0 : B.real.DefinableFun LRV (fun _ : Fin n → M => iVFZero) := by
    exact SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have he := hp.ofPred_eq h0
  apply real_definableOverBase
  apply (definableOver_iff_normalized_raw _ _ _).mpr
  constructor
  · rw [canonical_normalize_eq hc]
    exact (sortedUniverse_definable B.real (fun _ : Fin n => .vf)).raw_definable.inter he
  · exact fun _ h => h.1

end DiamondIntegral.Section5
