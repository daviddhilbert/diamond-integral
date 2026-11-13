import «section 3».ACFGenericDiagonalGraph
import «section 3».DiagonalBirationalKernels
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K] [CompatibleRing K]
variable {A : Type*} [AddCommGroup A] {n : ℕ}

/-- Actual definable graph invariance, rationality and inverse rationality
supply the equivariant birational map required by Reichstein--Youssin. -/
def acfDefinableDiagonalBirationalEquiv (E : Subfield K)
    (R : Set (Fin n ⊕ Fin n → K)) (hR : (E : Set K).Definable Language.ring R)
    (x y : Fin n → K) (hxy : Sum.elim x y ∈ R)
    (hu : ∀ u v w, Sum.elim u v ∈ R → Sum.elim u w ∈ R → v = w)
    (hv : ∀ z : Fin n → K, Sum.elim z y ∈ R → z = x)
    (hx : AlgebraicIndependent E x) (hy : AlgebraicIndependent E y)
    (a b : Fin n → A)
    (hscale : ∀ χ : Multiplicative A →* Eˣ,
      Sum.elim (fun i => ((χ (Multiplicative.ofAdd (a i)) : E) : K) * x i)
        (fun i => ((χ (Multiplicative.ofAdd (b i)) : E) : K) * y i) ∈ R) :
    DiagonalBirationalEquiv E a b where
  toAlgEquiv := acfGenericBirationalEquiv E R hR x y hxy
    (fun z hz => hu x z y hz hxy) hv hx hy
  equivariant χ z := acfGenericBirationalEquiv_diagonal E R hR x y hxy hu hv hx hy
    (fun i => χ (Multiplicative.ofAdd (a i)))
    (fun i => χ (Multiplicative.ofAdd (b i))) (hscale χ) z

/-- Classification of the weights of a genuine invariant definable
residue graph. All field-geometric steps are checked locally; only the
stated algebraic-group classification is the cited input. -/
theorem acf_definable_diagonal_monomial_weights (E : Subfield K) [IsAlgClosed E]
    (H : ReichsteinYoussinInput E A)
    (R : Set (Fin n ⊕ Fin n → K)) (hR : (E : Set K).Definable Language.ring R)
    (x y : Fin n → K) (hxy : Sum.elim x y ∈ R)
    (hu : ∀ u v w, Sum.elim u v ∈ R → Sum.elim u w ∈ R → v = w)
    (hv : ∀ z : Fin n → K, Sum.elim z y ∈ R → z = x)
    (hx : AlgebraicIndependent E x) (hy : AlgebraicIndependent E y)
    (a b : Fin n → A)
    (hgen : AddSubgroup.closure (Set.range a ∪ Set.range b) = ⊤)
    (hscale : ∀ χ : Multiplicative A →* Eˣ,
      Sum.elim (fun i => ((χ (Multiplicative.ofAdd (a i)) : E) : K) * x i)
        (fun i => ((χ (Multiplicative.ofAdd (b i)) : E) : K) * y i) ∈ R) :
    ∃ C : Matrix (Fin n) (Fin n) ℤ, IsUnit C.det ∧ ∀ i, b i = ∑ j, C i j • a j :=
  (acfDefinableDiagonalBirationalEquiv E R hR x y hxy hu hv hx hy a b hscale).monomial_weights H hgen

end DiamondIntegral.Section3
