import «section 3».GammaRVCodeLift
import «section 3».GammaVolumeCategories
import «section 2».Bases
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The accepted [19], Remark 2.28 and Lemma 2.29, retained as exact
replaceable inputs at their VF-generated real-base scope. Translation
constants are values of named nonzero RV points. The formulas are local
on a finite definable cover and are never asserted globally affine. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaIntegralAffineFormula (S : Set M) (k : ℕ) where
  linear : Matrix (Fin k) (Fin k) ℤ
  shift : Fin k → Section2.RV M
  named : ∀ i, (shift i).val.val ∈ S

def GammaIntegralAffineFormula.eval {S : Set M} {k : ℕ} (F : GammaIntegralAffineFormula S k)
    (α : Fin k → Values.Gamma (M := M)) : Fin k → Values.Gamma (M := M) :=
  fun i => Section2.rvFiniteValue (F.shift i) * ∏ j, (α j) ^ F.linear i j

def GammaIntegralAffineFormula.Unimodular {S : Set M} {k : ℕ}
    (F : GammaIntegralAffineFormula S k) : Prop := IsUnit F.linear.det

variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M}

def GammaPiecewiseGLZ {k : ℕ} (A B : GammaObject hc S k) (f : FamilyBijection A B) : Prop :=
  ∃ N, ∃ src : Fin N → Fin A.tags, ∃ dst : Fin N → Fin B.tags,
    ∃ cell : Fin N → GammaPiece hc S k,
    ∃ sub : ∀ q, (cell q).carrier ⊆ (A.piece (src q)).carrier,
    ∃ F : Fin N → GammaIntegralAffineFormula S k,
      (∀ q, (F q).Unimodular) ∧
      (∀ a : A.Carrier, ∃ q, src q = a.1 ∧ a.2.val ∈ (cell q).carrier) ∧
      (∀ q (a : cell q),
        let p : A.Carrier := ⟨src q, ⟨a.val, sub q a.property⟩⟩
        (f.equiv p).1 = dst q ∧ B.coordinates (f.equiv p) = (F q).eval (A.coordinates p))

def GammaUnaryPiecewiseIntegralAffine (I J : GammaPiece hc S 1) (f : Map I J) : Prop :=
  ∃ N, ∃ cell : Fin N → GammaPiece hc S 1,
    ∃ sub : ∀ q, (cell q).carrier ⊆ I.carrier,
    ∃ F : Fin N → GammaIntegralAffineFormula S 1,
      (∀ a : I, ∃ q, a.val ∈ (cell q).carrier) ∧
      (∀ q (a : cell q),
        (f ⟨a.val, sub q a.property⟩).val = (F q).eval a.val)

structure YinGammaAffineInput (C : BaseContext M)
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : Section2.VFGeneratedFieldBase C.base) where
  contraction : ∀ (I J : GammaPiece hc (C.base : Set M) 1) (f : Map I J)
    (F : Map (codePreimage I) (codePreimage J)),
    (∀ c, codeDecode J (F c) = f (codeDecode I c)) → GammaUnaryPiecewiseIntegralAffine I J f
  classification : ∀ {k : ℕ} (A B : GammaObject hc (C.base : Set M) k) (f : FamilyBijection A B),
    (∃ g : GammaHom A B, g.bijection = f) ↔ GammaPiecewiseGLZ A B f

theorem gammaHom_piecewiseGLZ {C : BaseContext M} {B : Section2.VFGeneratedFieldBase C.base}
    (H : YinGammaAffineInput C hc B) {k : ℕ} {A D : GammaObject hc (C.base : Set M) k}
    (f : GammaHom A D) : GammaPiecewiseGLZ A D f.bijection :=
  (H.classification A D f.bijection).mp ⟨f, rfl⟩

def gammaHomOfPiecewiseGLZ {C : BaseContext M} {B : Section2.VFGeneratedFieldBase C.base}
    (H : YinGammaAffineInput C hc B) {k : ℕ} {A D : GammaObject hc (C.base : Set M) k}
    (f : FamilyBijection A D) (hf : GammaPiecewiseGLZ A D f) : GammaHom A D :=
  Classical.choose ((H.classification A D f).mpr hf)

end DiamondIntegral.Section3
