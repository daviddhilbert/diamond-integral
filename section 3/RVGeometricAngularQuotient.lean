import «section 3».RVAngularCoordinateMaps
import «section 3».RVMixedValueMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def rvAngularMixedDomain (hc : CanonicalStructure.IsCanonical (M := M))
    (X : DefSet (rawRVUnitSpace (M := M) n) S) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) :
    DefSet ((rawRVUnitSpace K.zeroArity).prod ((volumeGammaSpace hc).power (Fin K.freeArity))) S :=
  (rvMixedValueProjectionMap hc (rvAngularCoordinateMap X E K).image).image

theorem rvAngularMixedDomain_carrier (hc : CanonicalStructure.IsCanonical (M := M))
    (X : DefSet (rawRVUnitSpace (M := M) n) S) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) :
    (rvAngularMixedDomain hc X E K).carrier = mixedValueQuotient rvUnitTupleValues (E.coordinateImage K) := by
  rw [rvAngularMixedDomain,rvMixedValueProjectionMap_image,rvAngularCoordinateMap_image]

/-- The actual definable mixed quotient recovers exactly the entire
original coordinate set by full Gamma preimage. -/
theorem rvAngularMixedDomain_full_preimage (hc : CanonicalStructure.IsCanonical (M := M))
    (X : DefSet (rawRVUnitSpace (M := M) n) S) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) :
    mixedValueProjection rvUnitTupleValues ⁻¹' (rvAngularMixedDomain hc X E K).carrier =
      (rvAngularCoordinateMap X E K).image.carrier := by
  rw [rvAngularMixedDomain_carrier,rvAngularCoordinateMap_image]
  exact E.full_value_preimage K

def rvAngularResidueDomain (hc : CanonicalStructure.IsCanonical (M := M))
    (X : DefSet (rawRVUnitSpace (M := M) n) S) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) : DefSet (rawRVUnitSpace K.zeroArity) S :=
  (Map.fst (rawRVUnitSpace K.zeroArity) ((volumeGammaSpace hc).power (Fin K.freeArity)) S
    (rvAngularMixedDomain hc X E K)).image

theorem rvAngularResidueDomain_carrier (hc : CanonicalStructure.IsCanonical (M := M))
    (X : DefSet (rawRVUnitSpace (M := M) n) S) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) :
    (rvAngularResidueDomain hc X E K).carrier = Prod.fst '' E.coordinateImage K := by
  have hf : (rvAngularResidueDomain hc X E K).carrier = Prod.fst '' (rvAngularMixedDomain hc X E K).carrier := by
    ext y
    exact ⟨fun ⟨x,hx⟩ => ⟨x.val,x.property,hx⟩,fun ⟨x,hx,he⟩ => ⟨⟨x,hx⟩,he⟩⟩
  rw [hf,rvAngularMixedDomain_carrier,mixedValueQuotient_residue_projection]
  rfl

theorem rvAngularResidueDomain_finite_values (hc : CanonicalStructure.IsCanonical (M := M))
    (X : DefSet (rawRVUnitSpace (M := M) n) S) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) :
    (rvUnitTupleValues '' (rvAngularResidueDomain hc X E K).carrier).Finite := by
  rw [rvAngularResidueDomain_carrier,RVAngularCell.coordinateImage,Set.image_image,Set.image_image]
  exact E.residue_tuple_values_finite K
end DiamondIntegral.Section3
