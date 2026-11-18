import «section 3».GammaMeasuredIsomorphismSchemata
import «section 3».GammaMeasuredRowPresentations
import «section 3».GammaMeasuredCodeProducts
import «section 3».GammaUniversalIsomorphismMaps
import «section 3».GammaNativeMeasuredIsomorphisms
import IntegrationSection6.GammaSchemaChartRows

/-! A valid Gamma chart realizes an actual measured RV isomorphism on
the stated row objects. The map is the existing native chart realization;
its Gamma-weight proof works for every density representative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a b k : ℕ} {sp : Fin p → SortTag}

theorem GammaMeasuredRVIsoSchema.realizeOn
    (F : GammaMeasuredRVIsoSchema hc B p a b k sp) (z : Fin p → M) (hz : F.valid z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1)
      ((essentialFiniteVolumeSchema F.source.object).rowDomain z)
      ((essentialFiniteVolumeSchema F.source.object).rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b (k+1)
      ((essentialFiniteVolumeSchema F.target.object).rowDomain z)
      ((essentialFiniteVolumeSchema F.target.object).rowVolume z)) :
    Nonempty (GammaGroundMeasuredRVHom (F.source.presentedRowObject z hz.1 P)
      (F.target.presentedRowObject z hz.2.1 Q)) := by
  let e := F.ordinary.realizeChart z hz.2.2.1 P Q
  let EI := gammaUniversalIsoAt P.toGamma Q.toGamma e
  let ω := F.source.presentedRowForm z hz.1 P
  let π := F.target.presentedRowForm z hz.2.1 Q
  refine ⟨gammaNativeMeasuredNormalizationHom ω π EI (fun u => ?_)⟩
  let v := (Section5.nativeRVGroundIso EI).map u
  let u0 := Section5.nativeRVGroundDomainEquiv (gammaUniversalObject P.toGamma) u
  obtain ⟨c,hcValue⟩ := (volumeGammaSpace hc).onto (ω u).val
  obtain ⟨d,hdValue⟩ := (volumeGammaSpace hc).onto (π v).val
  let aV := (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) u).val
  let bV := (Section5.nativeRVGroundVolume (gammaUniversalObject Q.toGamma) v).val
  let μ := Fin.append aV (gammaVolumeCodeRV c)
  let ν := Fin.append bV (gammaVolumeCodeRV d)
  have hWeightedU : Fin.append (Fin.append z (rvValues u.val)) (rvValues μ) ∈
      weightedVolumeGraph F.source.toRVTemplate := by
    rw [gammaMeasuredCodeProduct_raw]
    exact (weightedVolumeGraph_append F.source.toRVTemplate z (rvValues u.val) (rvValues aV) c.val).mpr
      ⟨F.source.presentedRow_volume z P u,F.source.presentedRow_density z hz.1 P u c hcValue⟩
  have hWeightedV : Fin.append (Fin.append z (rvValues v.val)) (rvValues ν) ∈
      weightedVolumeGraph F.target.toRVTemplate := by
    rw [gammaMeasuredCodeProduct_raw]
    exact (weightedVolumeGraph_append F.target.toRVTemplate z (rvValues v.val) (rvValues bV) d.val).mpr
      ⟨F.target.presentedRow_volume z Q v,F.target.presentedRow_density z hz.2.1 Q v d hdValue⟩
  have hChart : Fin.append (Fin.append z (rvValues u.val)) (rvValues v.val) ∈ F.chart :=
    F.ordinary.realizeChart_apply z hz.2.2.1 P Q u0
  have hBalance := volumeChartGammaRowValid_apply F.source.toRVTemplate F.target.toRVTemplate F.chart z hz.2.2.2
    (rvValues μ) (rvValues ν) (fun i => (μ i).property) (fun i => (ν i).property)
    (rvValues u.val) (rvValues v.val) hWeightedU hChart hWeightedV
  have hEq := ((rvProductGammaBalance_append ((k+1)+1) μ ν).mp hBalance).2.2
  exact (gammaMeasuredCodeProduct ω u aV c hcValue).symm.trans
    (hEq.trans (gammaMeasuredCodeProduct π v bV d hdValue))

end DiamondIntegral.Section3
