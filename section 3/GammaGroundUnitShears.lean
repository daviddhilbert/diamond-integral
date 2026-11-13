import «section 3».GammaGroundUnitPreimageProducts
import «section 3».RVCoefficientTranslations
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m : ℕ}

/-- Multiplicative stabilization turns any actual RV map into a
bijection by retaining its input and multiplying an additional free
unit tuple by its output. -/
def gammaGroundRVUnitShear
    (I : GammaGroundGammaPiece hc B n)
    (f : GammaGroundMap (gammaGroundRVUnitGammaPreimage I)
      (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m))) :
    GammaGroundBijection
      (gammaGroundRVUnitGammaPreimage (gammaGroundGammaAppendMap I
        (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))).image)
      (gammaGroundRVUnitGammaPreimage (gammaGroundGammaAppendMap I
        (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))).image) := by
  let U := GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m)
  let e := gammaGroundUnitPreimageProductBijection I
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))
  let S := gammaGroundRVUnitSkewBijection (gammaGroundRVUnitGammaPreimage I) U U f
    (fun _ _ _ => Set.mem_univ _) (fun _ _ _ => Set.mem_univ _)
  exact e.comp (S.comp e.symm)

/-- The stabilized map keeps the first RV tuple literally unchanged. -/
theorem gammaGroundRVUnitShear_at_product
    (I : GammaGroundGammaPiece hc B n)
    (f : GammaGroundMap (gammaGroundRVUnitGammaPreimage I)
      (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m)))
    (u : (gammaGroundRVUnitGammaPreimage I).prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m))) :
    ((gammaGroundRVUnitShear I f).map
      ((gammaGroundUnitPreimageProductBijection I
        (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))).map u)).val =
      Fin.append u.val.1 (fun i => (f ⟨u.val.1,u.property.1⟩).val i * u.val.2 i) := by
  let e := gammaGroundUnitPreimageProductBijection I
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))
  let U := GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m)
  let S := gammaGroundRVUnitSkewBijection (gammaGroundRVUnitGammaPreimage I) U U f
    (fun _ _ _ => Set.mem_univ _) (fun _ _ _ => Set.mem_univ _)
  change (e.map (S.map (e.map.inverse e.bijective (e.map u)))).val = _
  rw [GammaGroundMap.inverse_apply]
  rfl

end DiamondIntegral.Section3
