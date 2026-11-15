import «section 5».MonomialTorsorCoordinates
import «section 5».MonomialGammaGraphEuler
import «section 5».NativeUnitGammaValues
import «section 3».RVUnitGammaCodeBijection
import «section 4».Section3GammaRVCodeBridge

/-! The native bounded value of a full nonzero RV value preimage is its
actual Gamma Euler integral times every retained residue-torus factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVClassCuts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)


variable {n : ℕ} {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}

def GroundMonomialPiece.reconstructedTorsorDomain (P : GroundMonomialPiece X)
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1)))) :=
  (gammaGroundRVUnitTupleProductMap (P.reconstructedTorsorSource D)).image

def GroundMonomialPiece.reconstructedTorsorProductBijection (P : GroundMonomialPiece X)
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1)))) :
    GammaGroundBijection (P.reconstructedTorsorDomain D)
      (gammaGroundRVUnitTupleProductMap
        (P.residue.prod (gammaGroundRVUnitGammaPreimage (P.reconstructedGammaGraph D)))).image :=
  (gammaGroundRVUnitTupleProductBijection _).comp
    ((P.reconstructedTorsorBijection D).comp (gammaGroundRVUnitTupleProductBijection _).symm)

theorem GroundMonomialPiece.native_unit_value (P : GroundMonomialPiece X) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind P.source =
      nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind P.residue *
        nativeTorusClass B ^ P.split.freeArity *
        (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ kind P.split.freeArity
          (GammaIndicators.indicatorFamily B P.gamma.carrier (Section3GammaChartBridge.chart P.gamma).support_definable) :
            RESDimensionFreeReduction.Ring B) := by
  let f := (gammaGroundRVUnitTupleProductBijection _).comp P.coordinateBijection
  rw [nativeUnitRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind P.source _ f,
    nativeUnitRVSetValue_product, nativeUnitRVSetValue_gamma]
  ring

theorem GroundMonomialPiece.reconstructedTorsor_value
    (P : GroundMonomialPiece X)
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hD : ∀ α ∈ D.carrier, ∀ β ∈ D.carrier, Fin.init α = Fin.init β → α (Fin.last n) = β (Fin.last n))
    (hcomplete : ∀ x ∈ P.source.carrier, ∃ γ, Fin.snoc (rvUnitTupleValues x) γ ∈ D.carrier) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (P.reconstructedTorsorDomain D) =
      nativeTorusClass B * nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind P.source := by
  rw [nativeUnitRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
      (P.reconstructedTorsorProductBijection D),
    nativeUnitRVSetValue_product, nativeUnitRVSetValue_gamma,
    P.reconstructedGammaGraph_euler h00 linear hκ hs hr hγ hΓ kind D hD hcomplete,
    P.native_unit_value h00 linear hκ hs hr hγ hΓ kind, pow_succ]
  ring

end DiamondIntegral.Section5
