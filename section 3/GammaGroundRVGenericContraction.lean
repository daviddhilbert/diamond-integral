import «section 3».GammaGroundRVGenericTupleContraction
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

/-- Generic selection respects the actual Gamma target of an RV map.
This constructs an interpreted map; a bijective full RV lift is a
separate obligation. -/
theorem gammaGroundRVGeneric_contraction {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)))
    (w : GammaGroundMap (gammaGroundRVUnitGammaPreimage G) J) :
    ∃ h : GammaGroundMap G J,
      (gammaGroundRVGenericValueImage hs h00 B hsmall
        (w.equalizer (h.comp (gammaGroundFullPreimageValueMap G)))).carrier = G.carrier := by
  obtain ⟨h,hh⟩ := gammaGroundRVGeneric_tuple_contraction hκ hs h00 hsmall hγsmall G w.toUniv
  let E := w.toUniv.equalizer (h.comp (gammaGroundFullPreimageValueMap G))
  have hrange : ∀ γ : G, (h γ).val ∈ J.carrier := by
    intro γ
    have hγ : γ.val ∈ (gammaGroundRVGenericValueImage hs h00 B hsmall E).carrier := hh.symm ▸ γ.property
    obtain ⟨u,hu,hv⟩ := gammaGroundRVGenericValueImage_subset_values hs h00 B hsmall E hγ
    obtain ⟨a,ha,he⟩ := hu
    have hva : gammaGroundFullPreimageValueMap G a = γ :=
      Subtype.ext ((congrArg rvUnitTupleValues ha).trans hv)
    change (w a).val = (h (gammaGroundFullPreimageValueMap G a)).val at he
    rw [hva] at he
    exact he ▸ (w a).property
  exact ⟨h.corestrict hrange,hh⟩

/-- In particular every actual map between full RV preimages determines
an original-ground interpreted map between the corresponding Gamma sets. -/
theorem gammaGroundRVMap_generic_contraction {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)))
    (f : GammaGroundMap (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage J)) :
    ∃ h : GammaGroundMap G J,
      (gammaGroundRVGenericValueImage hs h00 B hsmall
        (((gammaGroundFullPreimageValueMap J).comp f).equalizer
          (h.comp (gammaGroundFullPreimageValueMap G)))).carrier = G.carrier :=
  gammaGroundRVGeneric_contraction hκ hs h00 hsmall hγsmall G J
    ((gammaGroundFullPreimageValueMap J).comp f)

end DiamondIntegral.Section3
