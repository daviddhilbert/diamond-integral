import «section 3».GammaMeasuredIsomorphismSchemata
import «section 3».GammaMeasuredCodeProducts

/-! A valid measured chart balances the actual Gamma density times
the structural volume product, for every pair of representative codes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a b k : ℕ} {sp : Fin p → SortTag}

theorem GammaMeasuredRVIsoSchema.chart_product
    (I : GammaMeasuredRVIsoSchema hc B p a b k sp) (z : Fin p → M) (hz : I.valid z)
    (x : Fin a → CanonicalRV.RVSort M) (y : Fin b → CanonicalRV.RVSort M)
    (u v : Fin (k+1) → CanonicalRV.RVSort M)
    (c e : (volumeGammaSpace hc).domain)
    (hX : I.source.object.rowVolume z x u) (hY : I.target.object.rowVolume z y v)
    (hC : I.source.rowDensity z x c) (hE : I.target.rowDensity z y e)
    (hChart : Fin.append (Fin.append z (rvValues x)) (rvValues y) ∈ I.chart) :
    Values.vrv (∏ j, Fin.append u (gammaVolumeCodeRV c) j) =
      Values.vrv (∏ j, Fin.append v (gammaVolumeCodeRV e) j) := by
  let μ := Fin.append u (gammaVolumeCodeRV c)
  let ν := Fin.append v (gammaVolumeCodeRV e)
  have hWeightedX : Fin.append (Fin.append z (rvValues x)) (rvValues μ) ∈
      weightedVolumeGraph I.source.toRVTemplate := by
    rw [gammaMeasuredCodeProduct_raw]
    exact (weightedVolumeGraph_append I.source.toRVTemplate z (rvValues x) (rvValues u) c.val).mpr ⟨hX,hC⟩
  have hWeightedY : Fin.append (Fin.append z (rvValues y)) (rvValues ν) ∈
      weightedVolumeGraph I.target.toRVTemplate := by
    rw [gammaMeasuredCodeProduct_raw]
    exact (weightedVolumeGraph_append I.target.toRVTemplate z (rvValues y) (rvValues v) e.val).mpr ⟨hY,hE⟩
  have h := volumeChartGammaRowValid_apply I.source.toRVTemplate I.target.toRVTemplate I.chart z hz.2.2.2
    (rvValues μ) (rvValues ν) (fun j => (μ j).property) (fun j => (ν j).property)
    (rvValues x) (rvValues y) hWeightedX hChart hWeightedY
  exact ((rvProductGammaBalance_append ((k+1)+1) μ ν).mp h).2.2

end DiamondIntegral.Section3
