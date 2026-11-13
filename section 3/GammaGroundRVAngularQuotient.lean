import «section 3».GammaGroundRVAngularCoordinates
import «section 3».RVMixedValueMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p m n : ℕ}

def gammaGroundRVMixedValueProjection
    (X : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod (rawRVUnitSpace m))) :
    GammaGroundMap X (GammaGroundDefSet.univ hc B ((rawRVUnitSpace p).prod ((volumeGammaSpace hc).power (Fin m)))) :=
  GammaGroundMap.ofGlobal _ _
    (rvMixedValueProjectionMap hc (DefSet.univ ((rawRVUnitSpace p).prod (rawRVUnitSpace m)) B.real))
    (fun _ => Set.mem_univ _)

theorem gammaGroundRVMixedValueProjection_image
    (X : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod (rawRVUnitSpace m))) :
    (gammaGroundRVMixedValueProjection X).image.carrier = mixedValueQuotient rvUnitTupleValues X.carrier := by
  ext y
  exact ⟨fun ⟨x,hx⟩ => ⟨x.val,x.property,hx⟩,fun ⟨x,hx,he⟩ => ⟨⟨x,hx⟩,he⟩⟩

def gammaGroundRVAngularCoordinateBijection
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    GammaGroundBijection X (gammaGroundRVAngularCoordinateMap X E K).image :=
  ⟨(gammaGroundRVAngularCoordinateMap X E K).toImage,
    (gammaGroundRVAngularCoordinateMap X E K).toImage_bijective (gammaGroundRVAngularCoordinateMap_injective X E K)⟩

def gammaGroundRVAngularMixedDomain
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    GammaGroundDefSet hc B ((rawRVUnitSpace K.zeroArity).prod ((volumeGammaSpace hc).power (Fin K.freeArity))) :=
  (gammaGroundRVMixedValueProjection (gammaGroundRVAngularCoordinateMap X E K).image).image

theorem gammaGroundRVAngularMixedDomain_carrier
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    (gammaGroundRVAngularMixedDomain X E K).carrier = mixedValueQuotient rvUnitTupleValues (E.coordinateImage K) := by
  rw [gammaGroundRVAngularMixedDomain,gammaGroundRVMixedValueProjection_image,gammaGroundRVAngularCoordinateMap_image]

theorem gammaGroundRVAngularMixedDomain_full_preimage
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    mixedValueProjection rvUnitTupleValues ⁻¹' (gammaGroundRVAngularMixedDomain X E K).carrier =
      (gammaGroundRVAngularCoordinateMap X E K).image.carrier := by
  rw [gammaGroundRVAngularMixedDomain_carrier,gammaGroundRVAngularCoordinateMap_image]
  exact E.full_value_preimage K

def gammaGroundRVAngularResidueDomain
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) K.zeroArity) :=
  (GammaGroundMap.ofGlobal (gammaGroundRVAngularMixedDomain X E K) (GammaGroundDefSet.univ hc B (rawRVUnitSpace K.zeroArity))
    (universalProductFst (rawRVUnitSpace K.zeroArity) ((volumeGammaSpace hc).power (Fin K.freeArity)) B.real)
    (fun _ => Set.mem_univ _)).image

theorem gammaGroundRVAngularResidueDomain_carrier
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    (gammaGroundRVAngularResidueDomain X E K).carrier = Prod.fst '' E.coordinateImage K := by
  have hf : (gammaGroundRVAngularResidueDomain X E K).carrier = Prod.fst '' (gammaGroundRVAngularMixedDomain X E K).carrier := by
    ext y
    exact ⟨fun ⟨x,hx⟩ => ⟨x.val,x.property,hx⟩,fun ⟨x,hx,he⟩ => ⟨⟨x,hx⟩,he⟩⟩
  rw [hf,gammaGroundRVAngularMixedDomain_carrier,mixedValueQuotient_residue_projection]
  rfl

theorem gammaGroundRVAngularResidueDomain_finite_values
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    (rvUnitTupleValues '' (gammaGroundRVAngularResidueDomain X E K).carrier).Finite := by
  rw [gammaGroundRVAngularResidueDomain_carrier,RVAngularCell.coordinateImage,Set.image_image,Set.image_image]
  exact E.residue_tuple_values_finite K
end DiamondIntegral.Section3
