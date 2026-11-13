import «section 3».RVAngularLabelDegree
import «section 3».RVAngularGraphRigidity
import «section 3».RVAngularCellFullFibres
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n k : ℕ}

/-- Every angular graph chart containing a Gamma-generic input has a
square unimodular free input block; matching arity is proved from the label. -/
theorem gammaGroundRVAngular_generic_graph_block {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) (I : Fin k → Fin n) (x : X)
    (hg : GammaTupleIndependentOver B (fun i => rvUnitValueHom (x.val (I i))))
    (Y : GammaGroundDefSet hc B (rawRVSpace (M := M) k)) (f : GammaGroundMap X Y) (hf : f.FiniteFibres)
    (hinj : Set.InjOn (fun z => z ∘ I) X.carrier) :
    ∃ e : Fin K.freeArity ≃ Fin k,
      IsUnit (Matrix.submatrix (E.inverseFreeMatrix K) (I ∘ e) id).det := by
  have h := gammaGroundRVAngularCell_generic_arity_eq_label hκ hs h00 hsmall hγsmall hΓ X E K I x hg Y f hf
  let e : Fin K.freeArity ≃ Fin k := finCongr h
  refine ⟨e,?_⟩
  apply rvAngularGraph_free_block_unimodular h00 E K (I ∘ e) (E.coordinateEquiv K x.val).1
    (rvUnitTupleValues (E.coordinateEquiv K x.val).2)
  · exact fun u hu => E.coordinate_full_fibre K x.val x.property u hu
  · intro a ha b hb hab
    apply hinj ha hb
    funext i
    have hi := congrFun hab (e.symm i)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hi
end DiamondIntegral.Section3
