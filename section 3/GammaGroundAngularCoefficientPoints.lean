import «section 3».GammaGroundAngularResiduePoints
import «section 3».GammaGroundRVSingletonImages
import «section 3».RVUnitRectangularMonomials
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n p : ℕ}

theorem gammaGroundRVAngularProduct_residue_image_point_definable
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) (I : Fin K.freeArity → Fin n)
    (hunit : IsUnit (Matrix.submatrix (E.inverseFreeMatrix K) I id).det)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) K.zeroArity))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin K.freeArity))) (hG : G.carrier.Nonempty)
    (hrect : ∀ r ∈ R.carrier, ∀ u, rvUnitTupleValues u ∈ G.carrier →
      (E.coordinateEquiv K).symm (r,u) ∈ X.carrier)
    (hinj : Set.InjOn (fun z => z ∘ I) X.carrier)
    (S : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p)) (f : GammaGroundMap R S) (r : R) :
    ∀ i, DefinableClosureAtBase B .rv (rvUnitValues (f r).val i) := by
  obtain ⟨Q,hsub,hr,hQ⟩ := gammaGroundRVAngularProduct_residue_singleton_piece X E K I hunit R hR G hG hrect hinj r
  letI : Subsingleton Q := hQ
  exact gammaGroundRVUnitMap_subsingleton_image_point_definable Q S (f.restrict hsub) ⟨r.val,hr⟩

/-- The inverse graph-chart coefficients are actual old-ground RV
points, rather than coefficients named only at an auxiliary residue point. -/
theorem gammaGroundRVAngularProduct_inverse_coefficients_definable
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) (I : Fin K.freeArity → Fin n)
    (hunit : IsUnit (Matrix.submatrix (E.inverseFreeMatrix K) I id).det)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) K.zeroArity))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin K.freeArity))) (hG : G.carrier.Nonempty)
    (hrect : ∀ r ∈ R.carrier, ∀ u, rvUnitTupleValues u ∈ G.carrier →
      (E.coordinateEquiv K).symm (r,u) ∈ X.carrier)
    (hinj : Set.InjOn (fun z => z ∘ I) X.carrier) (r : R) :
    ∀ i, DefinableClosureAtBase B .rv (rvUnitValues (E.inverseResidueCoefficient K r.val) i) :=
  gammaGroundRVAngularProduct_residue_image_point_definable X E K I hunit R hR G hG hrect hinj _
    (gammaGroundRVUnitRectangularMonomialMap R
      (fun i j => integerBasisInverseMatrix E.basis i (K.zeroIndex j))) r
end DiamondIntegral.Section3
