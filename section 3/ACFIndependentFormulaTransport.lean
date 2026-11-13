import «section 3».DiagonalRationalActions
import «section 3».ACFSubfieldFormulaTransport
import «section 3».ACFGenericTargetIndependence
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K] [CompatibleRing K] {n : ℕ}

/-- All independent tuples of a fixed arity have the same pure-field
type over their coefficient field, proved without an ambient automorphism. -/
theorem acf_independent_formula_iff (E : Subfield K)
    (x y : Fin n → K) (hx : AlgebraicIndependent E x) (hy : AlgebraicIndependent E y)
    (φ : Language.ring.Formula (E ⊕ Fin n)) :
    φ.Realize (Sum.elim E.subtype x) ↔ φ.Realize (Sum.elim E.subtype y) := by
  let F := IntermediateField.adjoin E (Set.range x)
  let G := IntermediateField.adjoin E (Set.range y)
  let σ : F →ₐ[E] K := G.val.comp (hy.aevalEquivField.toAlgHom.comp hx.aevalEquivField.symm.toAlgHom)
  let u : Fin n → F := fun i => ⟨x i,IntermediateField.subset_adjoin E _ (Set.mem_range_self i)⟩
  have hu (i : Fin n) : hx.aevalEquivField (torusRationalVariable E i) = u i := by
    apply Subtype.ext
    rw [torusRationalVariable,hx.aevalEquivField_algebraMap_apply_coe]
    simp [u]
  have hσ (i : Fin n) : σ (u i) = y i := by
    rw [← hu i]
    change (hy.aevalEquivField (hx.aevalEquivField.symm (hx.aevalEquivField (torusRationalVariable E i))) : K) = y i
    rw [AlgEquiv.symm_apply_apply,torusRationalVariable,hy.aevalEquivField_algebraMap_apply_coe]
    simp
  have he := acf_formula_intermediate_embedding E F σ φ u
  simpa only [u,hσ] using he

/-- A definable residue set either contains every independent tuple or
contains none; this is the uniqueness needed for a generic value branch. -/
theorem acf_independent_definable_iff (E : Subfield K)
    (R : Set (Fin n → K)) (hR : (E : Set K).Definable Language.ring R)
    (x y : Fin n → K) (hx : AlgebraicIndependent E x) (hy : AlgebraicIndependent E y) :
    x ∈ R ↔ y ∈ R := by
  obtain ⟨φ,hφ⟩ := Set.definable_iff_exists_formula_sum.mp hR
  exact (Set.ext_iff.mp hφ x).trans
    ((acf_independent_formula_iff E x y hx hy φ).trans (Set.ext_iff.mp hφ y).symm)

end DiamondIntegral.Section3
