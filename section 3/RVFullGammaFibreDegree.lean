import «section 3».RVProductDegreeBound
import «section 3».GammaGroundRVUnitRES
import Section4.EarlierRVInputs
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {m k : ℕ}

/-- A nonempty full Gamma-preimage of arity m cannot map finite-to-one
to fewer than m RV coordinates. This also applies to a single value fibre. -/
theorem gammaGroundRVFullGammaPreimage_arity_le_of_finite_map {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m))) (hG : G.carrier.Nonempty)
    (Y : GammaGroundDefSet hc B (rawRVSpace (M := M) k))
    (f : GammaGroundMap (gammaGroundRVUnitGammaPreimage G) Y) (hf : f.FiniteFibres) : m ≤ k := by
  let R := GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) 0)
  let r : R := ⟨Fin.elim0,Set.mem_univ _⟩
  let p := GammaGroundMap.prodSnd R (gammaGroundRVUnitGammaPreimage G)
  have hp : Function.Injective p := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact i.elim0
    · exact congrArg Subtype.val hab
  have h := gammaGroundRVProduct_residue_rank_add_le (rvExchangeInput_of_earlier hκ hs h00)
    hκ hs h00 (gammaRVAlgebraicityInput_of_earlier hκ hs h00) hsmall R G hG Y (f.comp p)
    (hf.comp (GammaGroundMap.finiteFibres_of_injective hp)) r
  exact (Nat.le_add_left m _).trans h

theorem gammaGroundRVFullGammaPreimage_arity_le_of_unit_map {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m))) (hG : G.carrier.Nonempty)
    (Y : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) k))
    (f : GammaGroundMap (gammaGroundRVUnitGammaPreimage G) Y) (hf : f.FiniteFibres) : m ≤ k :=
  gammaGroundRVFullGammaPreimage_arity_le_of_finite_map hκ hs h00 hsmall G hG _
    ((gammaGroundRVUnitToRVMap Y).comp f)
    ((GammaGroundMap.finiteFibres_of_injective (gammaGroundRVUnitToRVMap_injective Y)).comp hf)
end DiamondIntegral.Section3
