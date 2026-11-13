import «section 3».ACFGenericBirationalFields
import «section 3».ACFSubfieldFormulaTransport
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
noncomputable section
namespace DiamondIntegral.Section3
variable {E K : Type*} [Field E] [Field K] [Algebra E K] {n : ℕ}

/-- Rational-function homomorphisms are determined by the coordinates. -/
theorem torusRational_algHom_ext {L : Type*} [Field L] [Algebra E L]
    (f g : TorusRationalFunction E n →ₐ[E] L)
    (h : ∀ i, f (torusRationalVariable E i) = g (torusRationalVariable E i)) : f = g := by
  apply AlgHom.toRingHom_injective
  apply IsFractionRing.ringHom_ext (A := MvPolynomial (Fin n) E)
  have hp : f.comp (IsScalarTower.toAlgHom E (MvPolynomial (Fin n) E) _) =
      g.comp (IsScalarTower.toAlgHom E (MvPolynomial (Fin n) E) _) := by
    apply MvPolynomial.algHom_ext
    intro i
    exact h i
  intro p
  exact AlgHom.congr_fun hp p

def genericFieldDiagonalEquiv (x : Fin n → K) (hx : AlgebraicIndependent E x)
    (a : Fin n → Eˣ) :
    IntermediateField.adjoin E (Set.range x) ≃ₐ[E] IntermediateField.adjoin E (Set.range x) :=
  (hx.aevalEquivField.symm.trans (diagonalRationalEquiv a)).trans hx.aevalEquivField

@[simp] theorem genericFieldDiagonalEquiv_coordinate (x : Fin n → K)
    (hx : AlgebraicIndependent E x) (a : Fin n → Eˣ) (i : Fin n) :
    (genericFieldDiagonalEquiv x hx a
      ⟨x i,IntermediateField.subset_adjoin E _ (Set.mem_range_self i)⟩ : K) =
      algebraMap E K (a i : E) * x i := by
  have hv : hx.aevalEquivField (torusRationalVariable E i) =
      ⟨x i,IntermediateField.subset_adjoin E _ (Set.mem_range_self i)⟩ := by
    apply Subtype.ext
    rw [torusRationalVariable,hx.aevalEquivField_algebraMap_apply_coe]
    simp
  rw [← hv]
  change ((hx.aevalEquivField
    (diagonalRationalEquiv a (hx.aevalEquivField.symm
      (hx.aevalEquivField (torusRationalVariable E i))))) : K) = _
  rw [AlgEquiv.symm_apply_apply,diagonalRationalEquiv_variable,map_mul]
  simp [hv]

end DiamondIntegral.Section3
