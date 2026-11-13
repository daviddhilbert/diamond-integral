import «section 3».GammaGroundGenericDomainPartitions
import «section 3».GammaGroundGenericFibreTests
import «section 3».GammaGroundPiecewiseValueMaps
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def gammaGroundFullPreimageValueMap
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n))) :
    GammaGroundMap (gammaGroundRVUnitGammaPreimage G) G :=
  (GammaGroundMap.ofGlobal _ (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n)))
    (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)).corestrict (fun a => a.property)

/-- Every original-ground Gamma-valued RV map on full preimages has a
uniform definable generic value on each fibre. The resulting interpreted
Gamma map is not yet asserted to possess a bijective RV lift. -/
theorem gammaGroundRVGeneric_scalar_contraction {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (w : GammaGroundMap (gammaGroundRVUnitGammaPreimage G)
      (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    ∃ h : GammaGroundMap G (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)),
      (gammaGroundRVGenericValueImage hs h00 B hsmall
        (w.equalizer (h.comp (gammaGroundFullPreimageValueMap G)))).carrier = G.carrier := by
  let A := gammaGroundRVUnitGammaPreimage G
  obtain ⟨N,Q,F,hQ,hdis,hcov,hF⟩ := gammaGroundRVUnitGammaForm_value_partition hκ.le hs h00 hsmall hγsmall A w
  have hpart : ∀ u : A, ∃! j, u.val ∈ (Q j).carrier := by
    intro u
    obtain ⟨j,hj⟩ := (hcov u.val).mp u.property
    refine ⟨j,hj,?_⟩
    intro k hk
    by_contra hne
    exact Set.disjoint_left.mp (hdis k j hne) hk hj
  let P := fun j => gammaGroundRVGenericValueImage hs h00 B hsmall (Q j)
  obtain ⟨hP,hcover⟩ := gammaGroundRVGenericValueImage_partition hs h00 B hsmall hκ G Q hQ hpart
  obtain ⟨h,hh⟩ := gammaGroundGamma_piecewise_value_map G P hP hcover F
  let E := w.equalizer (h.comp (gammaGroundFullPreimageValueMap G))
  refine ⟨h,?_⟩
  apply Set.Subset.antisymm
  · intro γ hγ
    obtain ⟨u,hu,hval⟩ := gammaGroundRVGenericValueImage_subset_values hs h00 B hsmall E hγ
    exact hval ▸ (w.equalizer_subset (h.comp (gammaGroundFullPreimageValueMap G)) hu)
  · intro γ hγ
    obtain ⟨j,hj,_⟩ := hcover γ hγ
    have hsub : ∀ u : Fin n → (CanonicalRV.RVSort M)ˣ,
        rvUnitTupleValues u = γ → u ∈ (Q j).carrier → u ∈ E.carrier := by
      intro u hu huQ
      let a : A := ⟨u,hQ j huQ⟩
      refine ⟨a,rfl,?_⟩
      have hv : (gammaGroundFullPreimageValueMap G a).val = γ := hu
      have hp : (gammaGroundFullPreimageValueMap G a).val ∈ (P j).carrier := hv.symm ▸ hj
      have hs' := hh j (gammaGroundFullPreimageValueMap G a) hp
      have hw := hF j a huQ
      exact hw.symm.trans hs'.symm
    exact gammaGroundGeneric_mono_on_fibre hs h00 B hsmall hκ (Q j) E γ hsub hj

end DiamondIntegral.Section3
