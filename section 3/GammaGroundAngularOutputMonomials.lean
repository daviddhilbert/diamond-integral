import «section 3».GammaGroundAngularCoefficientPoints
import «section 3».RVAngularOutputMonomials
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n l : ℕ}

/-- The output on a square graph product chart is an integral monomial
in its original input coordinates with an actual original-ground RV coefficient. -/
theorem gammaGroundRVAngularProduct_output_monomial
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) (I : Fin K.freeArity → Fin n) (O : Fin l → Fin n)
    (hunit : IsUnit (Matrix.submatrix (E.inverseFreeMatrix K) I id).det)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) K.zeroArity))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin K.freeArity))) (hG : G.carrier.Nonempty)
    (hrect : ∀ r ∈ R.carrier, ∀ u, rvUnitTupleValues u ∈ G.carrier →
      (E.coordinateEquiv K).symm (r,u) ∈ X.carrier)
    (hinj : Set.InjOn (fun z => z ∘ I) X.carrier) (r : R) :
    ∃ c : Fin l → (CanonicalRV.RVSort M)ˣ,
      (∀ j, DefinableClosureAtBase B .rv (rvUnitValues c j)) ∧
      ∀ u : Fin K.freeArity → (CanonicalRV.RVSort M)ˣ,
        (E.coordinateEquiv K).symm (r.val,u) ∘ O = c * integerMonomialMap (E.outputMonomialMatrix K I O)
          ((E.coordinateEquiv K).symm (r.val,u) ∘ I) := by
  let D := E.outputCoefficientMatrix K I O
  have hc : ∀ j, DefinableClosureAtBase B .rv (rvUnitValues (integerMonomialMap D r.val) j) :=
    gammaGroundRVAngularProduct_residue_image_point_definable X E K I hunit R hR G hG hrect hinj _
      (gammaGroundRVUnitRectangularMonomialMap R D) r
  exact ⟨integerMonomialMap D r.val,hc,fun u => E.coordinate_output_monomial K I O hunit r.val u⟩
end DiamondIntegral.Section3
