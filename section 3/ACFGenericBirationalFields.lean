import «section 3».ACFDefinableRelationFields
import «section 3».DiagonalRationalActions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K] [CompatibleRing K]
variable {n m : ℕ}

/-- A two-sided functional definable relation between independent
residue tuples gives an actual isomorphism of rational function fields. -/
def acfGenericBirationalEquiv (E : Subfield K)
    (R : Set (Fin n ⊕ Fin m → K)) (hR : (E : Set K).Definable Language.ring R)
    (x : Fin n → K) (y : Fin m → K) (hxy : Sum.elim x y ∈ R)
    (hu : ∀ z : Fin m → K, Sum.elim x z ∈ R → z = y)
    (hv : ∀ z : Fin n → K, Sum.elim z y ∈ R → z = x)
    (hx : AlgebraicIndependent E x) (hy : AlgebraicIndependent E y) :
    TorusRationalFunction E n ≃ₐ[E] TorusRationalFunction E m :=
  (hx.aevalEquivField.trans
    (IntermediateField.equivOfEq (acf_definable_bijection_adjoin_eq E R hR x y hxy hu hv))).trans
      hy.aevalEquivField.symm

/-- Evaluation into the ambient field commutes with this isomorphism. -/
theorem acfGenericBirationalEquiv_evaluate (E : Subfield K)
    (R : Set (Fin n ⊕ Fin m → K)) (hR : (E : Set K).Definable Language.ring R)
    (x : Fin n → K) (y : Fin m → K) (hxy : Sum.elim x y ∈ R)
    (hu : ∀ z : Fin m → K, Sum.elim x z ∈ R → z = y)
    (hv : ∀ z : Fin n → K, Sum.elim z y ∈ R → z = x)
    (hx : AlgebraicIndependent E x) (hy : AlgebraicIndependent E y)
    (z : TorusRationalFunction E n) :
    (hy.aevalEquivField (acfGenericBirationalEquiv E R hR x y hxy hu hv hx hy z) : K) =
      (hx.aevalEquivField z : K) := by
  simp [acfGenericBirationalEquiv]

end DiamondIntegral.Section3
