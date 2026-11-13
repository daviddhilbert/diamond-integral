import «section 3».RVAngularInverseMonomials
import «section 3».RVMonomialFibreRigidity
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

/-- On a graph chart whose free arity equals its input arity, injectivity
of the input projection forces its free monomial block to be unimodular. -/
theorem rvAngularGraph_free_block_unimodular (h00 : M ⊨ Axioms.ACVF00)
    {A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)} (E : RVAngularCell A)
    (K : Section2.ZeroFaceChart (Set.range E.active)) (I : Fin K.freeArity → Fin n)
    (r : Fin K.zeroArity → (CanonicalRV.RVSort M)ˣ) (δ : Fin K.freeArity → Values.Gamma (M := M))
    (hfull : ∀ u, rvUnitTupleValues u = δ → (E.coordinateEquiv K).symm (r,u) ∈ A)
    (hinj : Set.InjOn (fun z => z ∘ I) A) :
    IsUnit (Matrix.submatrix (E.inverseFreeMatrix K) I id).det := by
  let F := Matrix.submatrix (E.inverseFreeMatrix K) I id
  let c := E.inverseResidueCoefficient K r ∘ I
  apply rvAffineMonomial_full_fibre_unimodular h00 F c δ
  intro u hu v hv huv
  have hp : (E.coordinateEquiv K).symm (r,u) ∘ I = (E.coordinateEquiv K).symm (r,v) ∘ I := by
    rw [E.coordinateEquiv_symm_monomial K r u,E.coordinateEquiv_symm_monomial K r v]
    exact huv
  have he := congrArg (E.coordinateEquiv K) (hinj (hfull u hu) (hfull v hv) hp)
  rw [(E.coordinateEquiv K).apply_symm_apply,(E.coordinateEquiv K).apply_symm_apply] at he
  exact congrArg Prod.snd he
end DiamondIntegral.Section3
