import «section 3».GammaGroundRVGenericScalarContraction
import «section 3».GammaGroundMapTuples
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- The generic value tuple of an actual RV map is definable over its
original mixed ground, including when the target tuple is empty. -/
theorem gammaGroundRVGeneric_tuple_contraction {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (w : GammaGroundMap (gammaGroundRVUnitGammaPreimage G)
      (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))) :
    ∃ h : GammaGroundMap G (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m))),
      (gammaGroundRVGenericValueImage hs h00 B hsmall
        (w.equalizer (h.comp (gammaGroundFullPreimageValueMap G)))).carrier = G.carrier := by
  let A := gammaGroundRVUnitGammaPreimage G
  let coordinate (i : Fin m) : GammaGroundMap
      (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))
      (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)) :=
    GammaGroundMap.ofReal (universalPowerCoordinate (volumeGammaSpace hc) B.real i)
  let wi := fun i => (coordinate i).comp w
  choose hi hhi using fun i : Fin m =>
    gammaGroundRVGeneric_scalar_contraction hκ hs h00 hsmall hγsmall G (wi i)
  let h := GammaGroundMap.tuple hi
  let E := w.equalizer (h.comp (gammaGroundFullPreimageValueMap G))
  let Ei := fun i => (wi i).equalizer ((hi i).comp (gammaGroundFullPreimageValueMap G))
  let F : Option (Fin m) → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) :=
    fun o => o.elim E Ei
  refine ⟨h,Set.Subset.antisymm ?_ ?_⟩
  · intro γ hγ
    obtain ⟨u,hu,hval⟩ := gammaGroundRVGenericValueImage_subset_values hs h00 B hsmall E hγ
    exact hval ▸ (w.equalizer_subset (h.comp (gammaGroundFullPreimageValueMap G)) hu)
  · intro γ hγ
    obtain ⟨u,hu,hF⟩ := gammaGroundGeneric_finite_fibre_test hs h00 B hsmall hκ F γ
    apply (hF none).mpr
    have huA : u ∈ A.carrier := by
      change rvUnitTupleValues u ∈ G.carrier
      rwa [hu]
    let a : A := ⟨u,huA⟩
    refine ⟨a,rfl,?_⟩
    funext i
    have hγi : γ ∈ (gammaGroundRVGenericValueImage hs h00 B hsmall (Ei i)).carrier :=
      (hhi i).symm ▸ hγ
    obtain ⟨b,hb,hbi⟩ := (hF (some i)).mp hγi
    have hba : b = a := Subtype.ext hb
    subst b
    exact hbi

end DiamondIntegral.Section3
