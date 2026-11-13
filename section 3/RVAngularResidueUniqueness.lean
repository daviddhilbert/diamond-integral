import «section 3».MonomialProductCoefficients
import «section 3».RVAngularInverseMonomials
import «section 3».RVUnitGammaMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

/-- Within one residue-value tuple, a graph product chart with a
unimodular free input block has at most one residue point. -/
theorem rvAngularProduct_residue_subsingleton
    {A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)} (E : RVAngularCell A)
    (K : Section2.ZeroFaceChart (Set.range E.active)) (I : Fin K.freeArity → Fin n)
    (hunit : IsUnit (Matrix.submatrix (E.inverseFreeMatrix K) I id).det)
    (R : Set (Fin K.zeroArity → (CanonicalRV.RVSort M)ˣ))
    (G : Set (Fin K.freeArity → Values.Gamma (M := M))) (hG : G.Nonempty)
    (hR : ∀ r ∈ R, ∀ s ∈ R, rvUnitTupleValues r = rvUnitTupleValues s)
    (hrect : ∀ r ∈ R, ∀ u, rvUnitTupleValues u ∈ G → (E.coordinateEquiv K).symm (r,u) ∈ A)
    (hinj : Set.InjOn (fun z => z ∘ I) A) : Subsingleton R := by
  let F := Matrix.submatrix (E.inverseFreeMatrix K) I id
  let c := fun r : R => E.inverseResidueCoefficient K r.val ∘ I
  obtain ⟨δ,hδ⟩ := hG
  obtain ⟨x,hx⟩ := rvUnitTupleValues_surjective K.freeArity δ
  have hcx : (fun i => rvUnitValueHom (x i)) ∈ G := by
    change rvUnitTupleValues x ∈ G
    rw [hx]
    exact hδ
  apply monomialProduct_subsingleton_of_constant_coefficient_values (rvUnitValueHom (M := M)) F hunit c G x hcx
  · intro r s
    funext i
    change rvUnitValueHom (E.inverseResidueCoefficient K r.val (I i)) =
      rvUnitValueHom (E.inverseResidueCoefficient K s.val (I i))
    simp only [RVAngularCell.inverseResidueCoefficient,integerMonomialMap,map_prod,map_zpow]
    apply Finset.prod_congr rfl
    intro j _
    exact congrArg (fun γ => γ ^ integerBasisInverseMatrix E.basis (I i) (K.zeroIndex j))
      (congrFun (hR r.val r.property s.val s.property) j)
  · rintro ⟨r,u⟩ ⟨s,v⟩ he
    have hp : (E.coordinateEquiv K).symm (r.val,u.val) ∘ I =
        (E.coordinateEquiv K).symm (s.val,v.val) ∘ I := by
      rw [E.coordinateEquiv_symm_monomial K r.val u.val,E.coordinateEquiv_symm_monomial K s.val v.val]
      exact he
    have hh := congrArg (E.coordinateEquiv K)
      (hinj (hrect r.val r.property u.val u.property) (hrect s.val s.property v.val v.property) hp)
    rw [(E.coordinateEquiv K).apply_symm_apply,(E.coordinateEquiv K).apply_symm_apply] at hh
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
end DiamondIntegral.Section3
