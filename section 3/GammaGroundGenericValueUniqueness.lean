import «section 3».GammaGroundRVGenericScalarContraction
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

/-- A map on full RV preimages determines at most one interpreted generic
value map, for any common definable target. -/
theorem gammaGroundRVGeneric_value_unique {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ)
    {R : Space LRV M} {D : GammaGroundDefSet hc B R}
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (w : GammaGroundMap (gammaGroundRVUnitGammaPreimage G) D)
    (h k : GammaGroundMap G D)
    (hh : (gammaGroundRVGenericValueImage hs h00 B hsmall
      (w.equalizer (h.comp (gammaGroundFullPreimageValueMap G)))).carrier = G.carrier)
    (hk : (gammaGroundRVGenericValueImage hs h00 B hsmall
      (w.equalizer (k.comp (gammaGroundFullPreimageValueMap G)))).carrier = G.carrier) : h = k := by
  let Eh := w.equalizer (h.comp (gammaGroundFullPreimageValueMap G))
  let Ek := w.equalizer (k.comp (gammaGroundFullPreimageValueMap G))
  let F : Bool → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) := fun b => if b then Ek else Eh
  apply GammaGroundMap.ext
  intro γ
  obtain ⟨u,hu,hF⟩ := gammaGroundGeneric_finite_fibre_test hs h00 B hsmall hκ F γ.val
  have hγh : γ.val ∈ (gammaGroundRVGenericValueImage hs h00 B hsmall Eh).carrier := hh.symm ▸ γ.property
  have hγk : γ.val ∈ (gammaGroundRVGenericValueImage hs h00 B hsmall Ek).carrier := hk.symm ▸ γ.property
  obtain ⟨a,ha,hwa⟩ := (hF false).mp hγh
  obtain ⟨b,hb,hwb⟩ := (hF true).mp hγk
  have hab : a = b := Subtype.ext (ha.trans hb.symm)
  subst b
  have hv : gammaGroundFullPreimageValueMap G a = γ := by
    apply Subtype.ext
    exact (congrArg rvUnitTupleValues ha).trans hu
  have he : (h (gammaGroundFullPreimageValueMap G a)).val =
      (k (gammaGroundFullPreimageValueMap G a)).val := hwa.symm.trans hwb
  rw [hv] at he
  exact Subtype.ext he

end DiamondIntegral.Section3
