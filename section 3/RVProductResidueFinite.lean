import «section 3».RVProductRESFactor
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- If the free Gamma factor exhausts the finite RV label degree, its
residue factor is finite as an actual set. -/
theorem gammaGroundRVProduct_finite_residue_of_full_label {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m))) (hG : G.carrier.Nonempty)
    (Y : GammaGroundDefSet hc B (rawRVSpace (M := M) m))
    (f : GammaGroundMap (R.prod (gammaGroundRVUnitGammaPreimage G)) Y) (hf : f.FiniteFibres) : R.carrier.Finite := by
  have hres : ∃ U : GammaGroundRESObject hc B 0, Nonempty (GammaGroundBijection R U.obj.domain) := by
    have ht := gammaGroundRVProduct_RES_factor (k := m) (m := m) (rvExchangeInput_of_earlier hκ hs h00)
      hκ hs h00 (gammaRVAlgebraicityInput_of_earlier hκ hs h00) hsmall R hR G hG Y f hf
    rw [Nat.sub_self] at ht
    exact ht
  obtain ⟨U,⟨e⟩⟩ := hres
  letI : Fintype U.obj.domain := U.obj.degree_zero_finite.fintype
  letI : Finite R := Finite.of_injective e.map e.bijective.1
  simpa using (Set.finite_range (fun r : R => r.val))
end DiamondIntegral.Section3
