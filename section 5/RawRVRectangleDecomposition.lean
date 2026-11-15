import «section 5».MonomialSourcePartitions
import «section 5».RawRVGammaFamilies
import «section 5».RawRVUnitPartitions
import «section 5».MonomialTorsorEvaluation

/-! Finite original-ground RV rectangles for every raw RV domain,
including zeros. Every source-to-product map is an actual bijection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ}

structure RawRVRectangle (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) where
  source : GammaGroundDefSet hc B (rawRVSpace (M := M) p)
  source_subset : source.carrier ⊆ X.carrier
  residueArity : ℕ
  freeArity : ℕ
  residue : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) residueArity)
  gamma : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin freeArity))
  residue_finite : (rvUnitTupleValues '' residue.carrier).Finite
  bijection : GammaGroundBijection source (residue.prod (gammaGroundRVUnitGammaPreimage gamma))

theorem raw_rv_rectangle_decomposition
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) :
    ∃ N : ℕ, ∃ C : Fin N → RawRVRectangle X,
      (∀ i j, i ≠ j → Disjoint (C i).source.carrier (C j).source.carrier) ∧
        ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (C i).source.carrier := by
  let e := gammaGroundRVNonzeroTupleCodeBijection h00 X
  let Y := rawRVGammaBaseCode X
  obtain ⟨N,P,hd,hcov⟩ := ground_monomial_source_partition hκ hs h00 hr hγ hΓ Y
  have hsub (i : Fin N) : (P i).source.carrier ⊆ Y.carrier := fun x hx => (hcov x).mpr ⟨i,hx⟩
  let C : Fin N → RawRVRectangle X := fun i => {
    source := e.inverseImage (P i).source
    source_subset := e.inverseImage_subset _
    residueArity := (P i).split.zeroArity
    freeArity := (P i).split.freeArity
    residue := (P i).residue
    gamma := (P i).gamma
    residue_finite := by rw [(P i).residue_values]; exact Set.finite_singleton _
    bijection := (P i).coordinateBijection.comp (e.restrictTarget (P i).source (hsub i)) }
  have hp := groundBijection_pullback_partition e (fun i => (P i).source) hd hcov
  exact ⟨N,C,hp.1,hp.2⟩

theorem RawRVRectangle.native_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    {X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)} (C : RawRVRectangle X) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind C.source =
      nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind C.residue * nativeTorusClass B ^ C.freeArity *
        (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ kind C.freeArity
          (GammaIndicators.indicatorFamily B C.gamma.carrier (Section3GammaChartBridge.chart C.gamma).support_definable) :
            RESDimensionFreeReduction.Ring B) := by
  have he := nativeRVSetValue_raw_unit_bijection h00 linear hκ hs hr hγ hΓ kind _ _
    ((gammaGroundRVUnitTupleProductBijection _).comp C.bijection)
  rw [he,nativeUnitRVSetValue_product,nativeUnitRVSetValue_gamma]
  ring

end DiamondIntegral.Section5
