import «section 5».MonomialGammaGraphSupports
import «section 5».GammaSingletonGraphEuler

/-! Reconstructed value-torsor supports have exactly the actual Gamma
Euler characteristic of their monomial-chart base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
open GammaIteratedIntegral GammaIndicators
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}

theorem GroundMonomialPiece.reconstructedGammaGraph_euler
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (P : GroundMonomialPiece X)
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hD : ∀ α ∈ D.carrier, ∀ β ∈ D.carrier, Fin.init α = Fin.init β → α (Fin.last n) = β (Fin.last n))
    (hcomplete : ∀ x ∈ P.source.carrier, ∃ γ, Fin.snoc (rvUnitTupleValues x) γ ∈ D.carrier) :
    integrateAll h00 hκ hs B hr hγ kind (P.split.freeArity+1)
      (indicatorFamily B (P.reconstructedGammaGraph D).carrier
        (Section3GammaChartBridge.chart (P.reconstructedGammaGraph D)).support_definable) =
    integrateAll h00 hκ hs B hr hγ kind P.split.freeArity
      (indicatorFamily B P.gamma.carrier (Section3GammaChartBridge.chart P.gamma).support_definable) := by
  apply gamma_singleton_graph_euler h00 linear hκ hs hr hγ hΓ kind P.gamma (P.reconstructedGammaGraph D)
  · intro η γ h
    exact ((P.reconstructedGammaGraph_row D η γ).mp h).1
  · exact P.reconstructedGammaGraph_existsUnique D hD hcomplete

end DiamondIntegral.Section5
