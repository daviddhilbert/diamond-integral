import «section 3».GammaGroundRVUnitRES
import «section 3».RVNormalizedMapRelations
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}
variable {A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}
variable {D : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m)}

/-- The actual map transported to its raw RV presentations. Both charts
are bijections over the original ground. -/
def GammaGroundMap.unitRaw (f : GammaGroundMap A D) :
    GammaGroundMap (gammaGroundRVUnitToRVMap A).image (gammaGroundRVUnitToRVMap D).image :=
  (gammaGroundRVUnitPresentationBijection D).map.comp
    (f.comp (gammaGroundRVUnitPresentationBijection A).symm.map)

@[simp] theorem GammaGroundMap.unitRaw_chart (f : GammaGroundMap A D) (a : A) :
    f.unitRaw ((gammaGroundRVUnitPresentationBijection A).map a) =
      (gammaGroundRVUnitPresentationBijection D).map (f a) := by
  change (gammaGroundRVUnitPresentationBijection D).map
    (f ((gammaGroundRVUnitPresentationBijection A).map.inverse
      (gammaGroundRVUnitPresentationBijection A).bijective
      ((gammaGroundRVUnitPresentationBijection A).map a))) = _
  rw [GammaGroundMap.inverse_apply]

theorem GammaGroundMap.unitRaw_injective (f : GammaGroundMap A D) (hf : Function.Injective f) :
    Function.Injective f.unitRaw :=
  (gammaGroundRVUnitPresentationBijection D).bijective.1.comp
    (hf.comp (gammaGroundRVUnitPresentationBijection A).symm.bijective.1)

/-- An actual normalized unit-map point is a point of the normalized
raw graph used by the pure-field rationality and weight arguments. -/
theorem rvNormalizedUnitMap_point (f : GammaGroundMap A D)
    (a : Fin n → (CanonicalRV.RVSort M)ˣ) (b : Fin m → (CanonicalRV.RVSort M)ˣ)
    (x : Fin n → ModelResidue M) (y : Fin m → ModelResidue M)
    (u : A) (hu : rvUnitValues u.val = rvNormalizedTuple a x)
    (hv : rvUnitValues (f u).val = rvNormalizedTuple b y) :
    Sum.elim x y ∈ rvNormalizedMapRelation f.unitRaw a b := by
  refine ⟨(gammaGroundRVUnitPresentationBijection A).map u,?_,?_⟩
  · funext i
    apply Subtype.ext
    exact congrFun hu i
  · rw [f.unitRaw_chart]
    funext j
    apply Subtype.ext
    exact congrFun hv j

end DiamondIntegral.Section3
