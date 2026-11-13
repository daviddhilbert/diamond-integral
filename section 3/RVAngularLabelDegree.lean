import «section 3».GammaGroundRVAngularProductMaps
import «section 3».RVAngularGenericArity
import «section 3».RVProductDegreeBound
import Section4.EarlierRVInputs
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

/-- The free arity of a nonempty angular cell is bounded by every actual
finite RV label degree on that cell. -/
theorem gammaGroundRVAngularCell_free_arity_le_label {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) (x : X)
    (Y : GammaGroundDefSet hc B (rawRVSpace (M := M) k)) (f : GammaGroundMap X Y) (hf : f.FiniteFibres) :
    K.freeArity ≤ k := by
  obtain ⟨N,R,G,Q,F,_,hsub,_,hcov,_⟩ :=
    gammaGroundRVAngularCell_product_maps hκ hs h00 hsmall hγsmall hΓ X E K
  obtain ⟨i,hi⟩ := (hcov x.val).mp x.property
  let a : Q i := ⟨x.val,hi⟩
  let p := (F i).map a
  let r : R i := ⟨p.val.1,p.property.1⟩
  have hG : (G i).carrier.Nonempty := ⟨rvUnitTupleValues p.val.2,p.property.2⟩
  let g := (f.restrict (hsub i)).comp (F i).symm.map
  have hg : g.FiniteFibres := (hf.comp (GammaGroundMap.finiteFibres_of_injective
    (show Function.Injective (GammaGroundMap.inclusion (hsub i)) from fun _ _ he =>
      Subtype.ext (congrArg (fun z : X => z.val) he)))).comp
    (GammaGroundMap.finiteFibres_of_injective (F i).symm.bijective.1)
  have hd := gammaGroundRVProduct_residue_rank_add_le (rvExchangeInput_of_earlier hκ hs h00)
    hκ hs h00 (gammaRVAlgebraicityInput_of_earlier hκ hs h00) hsmall (R i) (G i) hG Y g hg r
  exact (Nat.le_add_left K.freeArity _).trans hd

theorem gammaGroundRVAngularCell_generic_arity_eq_label {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) (I : Fin k → Fin n) (x : X)
    (hg : GammaTupleIndependentOver B (fun i => rvUnitValueHom (x.val (I i))))
    (Y : GammaGroundDefSet hc B (rawRVSpace (M := M) k)) (f : GammaGroundMap X Y) (hf : f.FiniteFibres) :
    K.freeArity = k :=
  Nat.le_antisymm (gammaGroundRVAngularCell_free_arity_le_label hκ hs h00 hsmall hγsmall hΓ X E K x Y f hf)
    (gammaGroundRVAngularCell_generic_projection_arity_le X E K I x hg)
end DiamondIntegral.Section3
