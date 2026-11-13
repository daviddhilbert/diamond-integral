import «section 3».RVUnitProductFiniteRank
import «section 3».RVProductRank
import «section 3».GammaGroundRVUnitProducts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m k : ℕ}

/-- Each full Gamma-fibre coordinate uses one of the available RV[k]
label degrees. The residue point contributes its actual algebraic rank. -/
theorem gammaGroundRVProduct_residue_rank_add_le
    (hex : RVExchangeInput (M := M)) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hγ : GammaRVAlgebraicityInput (M := M) κ) (hsmall : Cardinal.mk B.real < κ)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m))) (hG : G.carrier.Nonempty)
    (Y : GammaGroundDefSet hc B (rawRVSpace (M := M) k))
    (f : GammaGroundMap (R.prod (gammaGroundRVUnitGammaPreimage G)) Y) (hf : f.FiniteFibres)
    (r : R) : rvTupleRank hc hex B.real (fun i => (r.val i : CanonicalRV.RVSort M)) + m ≤ k := by
  obtain ⟨δ,hδ⟩ := hG
  obtain ⟨b,hval,hrank⟩ := rv_rank_extension_in_gamma_fibres hc hex hκ hs h00 B.real hsmall
    (fun i => (r.val i : CanonicalRV.RVSort M)) δ
  have hb0 : ∀ i, (b i).val ≠ iRVZero := by
    intro i hi
    exact (δ i).property ((hval i).symm.trans ((Values.vrv_eq_infinity_iff (b i)).mpr hi))
  let u : Fin m → (CanonicalRV.RVSort M)ˣ := fun i => Units.mk0 (b i)
    (fun h => hb0 i ((congrArg Subtype.val h).trans RVOperations.zero_val))
  have hu : rvUnitTupleValues u = δ := by
    funext i
    apply Subtype.ext
    exact hval i
  let x : R.prod (gammaGroundRVUnitGammaPreimage G) :=
    ⟨(r.val,u),r.property,by change rvUnitTupleValues u ∈ G.carrier; rwa [hu]⟩
  have hx := gammaGroundRVUnitProduct_rank_le_of_finite_map hex hκ hγ hsmall _ Y f hf x
  have he : rvUnitProductTuple x.val = Fin.append (fun i => (r.val i : CanonicalRV.RVSort M)) b := rfl
  rw [he] at hx
  exact hrank.trans hx

theorem gammaGroundRVProduct_residue_rank_le_sub
    (hex : RVExchangeInput (M := M)) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hγ : GammaRVAlgebraicityInput (M := M) κ) (hsmall : Cardinal.mk B.real < κ)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m))) (hG : G.carrier.Nonempty)
    (Y : GammaGroundDefSet hc B (rawRVSpace (M := M) k))
    (f : GammaGroundMap (R.prod (gammaGroundRVUnitGammaPreimage G)) Y) (hf : f.FiniteFibres)
    (r : R) : rvTupleRank hc hex B.real (fun i => (r.val i : CanonicalRV.RVSort M)) ≤ k-m :=
  Nat.le_sub_of_add_le (gammaGroundRVProduct_residue_rank_add_le hex hκ hs h00 hγ hsmall R G hG Y f hf r)
end DiamondIntegral.Section3
