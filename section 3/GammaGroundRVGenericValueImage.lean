import «section 3».RVGenericFinitePartition
import «section 3».GammaGroundRVUnitDomains
import «section 3».GammaGroundMapImages
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
variable {κ : Cardinal} {hc : CanonicalStructure.IsCanonical (M := M)}
variable (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
variable (hsmall : Cardinal.mk B.real < κ) {n : ℕ}

def gammaGroundRVGenericUnits (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) :=
  gammaGroundRVUnitSetOfBase (rvFullFibreGeneric (rvUnitValues '' A.carrier))
    (rvFullFibreGeneric_definableOverBase hc hs h00 B hsmall _
      ((gammaGroundRVUnit_definable_iff A.carrier).mp A.definable))

def gammaGroundRVGenericValueMap (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    GammaGroundMap (gammaGroundRVGenericUnits hs h00 B hsmall A)
      (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n))) :=
  GammaGroundMap.ofGlobal _ _ (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)

def gammaGroundRVGenericValueImage (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)) :=
  (gammaGroundRVGenericValueMap hs h00 B hsmall A).image

/-- The generic value image has the entire selected value fibre as its
RV preimage, over exactly the original Gamma ground. -/
theorem gammaGroundRVGenericValueImage_mem_iff
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (u : Fin n → (CanonicalRV.RVSort M)ˣ) :
    rvUnitTupleValues u ∈ (gammaGroundRVGenericValueImage hs h00 B hsmall A).carrier ↔
      rvUnitValues u ∈ rvFullFibreGeneric (rvUnitValues '' A.carrier) := by
  constructor
  · rintro ⟨v,hv⟩
    have he : rvUnitTupleValues v.val = rvUnitTupleValues u := hv
    exact (rvFullFibreGeneric_invariant _ _ _ (rvUnitTuples_same_of_values_eq v.val u he)).mp v.property
  · intro hu
    exact ⟨⟨u,hu⟩,rfl⟩

end DiamondIntegral.Section3
