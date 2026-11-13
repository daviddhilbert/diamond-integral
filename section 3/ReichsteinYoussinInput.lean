import «section 3».DiagonalRationalActions
import «section 3».DiagonalWeightFaithfulness
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] {n : ℕ}

def diagonalWeightScaling (w : Fin n → A) (χ : Multiplicative A →* Kˣ) :
    TorusRationalFunction K n ≃ₐ[K] TorusRationalFunction K n :=
  diagonalRationalEquiv (fun i => χ (Multiplicative.ofAdd (w i)))

/-- Equivariant birationality is an actual isomorphism of rational
function fields intertwining all diagonal character actions. -/
structure DiagonalBirationalEquiv (K : Type*) [Field K]
    {A : Type*} [AddCommGroup A] {n : ℕ} (a b : Fin n → A) where
  toAlgEquiv : TorusRationalFunction K n ≃ₐ[K] TorusRationalFunction K n
  equivariant : ∀ (χ : Multiplicative A →* Kˣ) (z : TorusRationalFunction K n),
    toAlgEquiv (diagonalWeightScaling a χ z) = diagonalWeightScaling b χ (toAlgEquiv z)

def DiagonalBirationalEquiv.refl (a : Fin n → A) : DiagonalBirationalEquiv K a a :=
  ⟨AlgEquiv.refl,fun _ _ => rfl⟩

def DiagonalBirationalEquiv.symm {a b : Fin n → A}
    (E : DiagonalBirationalEquiv K a b) : DiagonalBirationalEquiv K b a where
  toAlgEquiv := E.toAlgEquiv.symm
  equivariant χ z := by
    apply E.toAlgEquiv.injective
    rw [AlgEquiv.apply_symm_apply]
    exact (E.equivariant χ (E.toAlgEquiv.symm z)).trans
      (congrArg (diagonalWeightScaling b χ) (E.toAlgEquiv.apply_symm_apply z)) |>.symm

def DiagonalBirationalEquiv.trans {a b c : Fin n → A}
    (E : DiagonalBirationalEquiv K a b) (F : DiagonalBirationalEquiv K b c) :
    DiagonalBirationalEquiv K a c where
  toAlgEquiv := E.toAlgEquiv.trans F.toAlgEquiv
  equivariant χ z := by
    change F.toAlgEquiv (E.toAlgEquiv (diagonalWeightScaling a χ z)) = _
    rw [E.equivariant,F.equivariant]
    rfl

/-- Exact author-approved consequence of Reichstein--Youssin,
Pacific J. Math. 204 (2002), 223--246, Theorem 7.1 and Corollary 2.5.
The joint finite weight tuples generate the character group, and
faithfulness of both actual character actions is explicit. No ACVF
extraction or parameter-descent claim is included in this input. -/
structure ReichsteinYoussinInput (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (A : Type*) [AddCommGroup A] where
  classification : ∀ (n : ℕ) (a b : Fin n → A),
    AddSubgroup.closure (Set.range a ∪ Set.range b) = ⊤ →
    DiagonalWeightsFaithful Kˣ a → DiagonalWeightsFaithful Kˣ b →
    DiagonalBirationalEquiv K a b →
    ∃ C : Matrix (Fin n) (Fin n) ℤ, IsUnit C.det ∧ ∀ i, b i = ∑ j, C i j • a j

theorem reichsteinYoussin_monomial_weights [IsAlgClosed K] [CharZero K]
    (H : ReichsteinYoussinInput K A) (a b : Fin n → A)
    (ha : AddSubgroup.closure (Set.range a) = ⊤)
    (hb : AddSubgroup.closure (Set.range b) = ⊤)
    (E : DiagonalBirationalEquiv K a b) :
    ∃ C : Matrix (Fin n) (Fin n) ℤ, IsUnit C.det ∧ ∀ i, b i = ∑ j, C i j • a j :=
  H.classification n a b (by
    apply top_unique
    have h := AddSubgroup.closure_mono (Set.subset_union_left (s := Set.range a) (t := Set.range b))
    rw [ha] at h
    exact h)
    (diagonalWeightsFaithful_of_generators a ha) (diagonalWeightsFaithful_of_generators b hb) E

end DiamondIntegral.Section3
