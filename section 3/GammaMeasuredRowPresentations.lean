import «section 3».GammaMeasuredSchemaRowForms
import «section 3».GammaNativeMeasuredNormalization
import Integration7.EssentialFiniteVolumeSchemata

/-! Essential native finite-row presentations carry the actual Gamma
form realized by their complete density relation. Labels and the whole
structural volume tuple agree with the original schema literally. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}
variable (F : GammaMeasuredRVSchema hc B p a (k+1) sp) (z : Fin p → M) (hz : F.valid z)
variable (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1)
  ((essentialFiniteVolumeSchema F.object).rowDomain z) ((essentialFiniteVolumeSchema F.object).rowVolume z))

def GammaMeasuredRVSchema.presentedRowLabels :
    GammaGroundMap (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) (F.rowDomain z) :=
  GammaGroundMap.inclusion (fun r hr => by
    let u := Section5.nativeRVGroundDomainEquiv (hc := hc) (gammaUniversalObject P.toGamma) ⟨r,hr⟩
    have hu := P.domain_eq.le u.property
    obtain ⟨v,hv,_⟩ := (essentialFiniteVolumeSchema_rowDomain F.object z u.val).mp hu
    exact hz.1.2.2.1 _ _ hv)

def GammaMeasuredRVSchema.presentedRowForm :
    GammaGroundVolumeForm hc ⟨B.real ∪ Set.range z,B.gamma⟩
      (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :=
  (F.rowForm z hz).comp (F.presentedRowLabels z hz P)

def GammaMeasuredRVSchema.presentedRowObject :=
  gammaNativeMeasuredNormalization (gammaUniversalObject P.toGamma) (F.presentedRowForm z hz P)

theorem GammaMeasuredRVSchema.presentedRow_volume
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :
    F.object.rowVolume z u.val (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) u).val := by
  let v := Section5.nativeRVGroundDomainEquiv (hc := hc) (gammaUniversalObject P.toGamma) u
  have hP := ((P.graph_iff v.val (P.volume v).val).mp ⟨v,rfl,rfl⟩).2
  have hF := (essentialFiniteVolumeSchema_rowVolume F.object z v.val (P.volume v).val).mp hP
  have he : (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) u).val = (P.volume v).val :=
    gammaNativeRVGroundVolume_value (gammaUniversalObject P.toGamma) u
  exact Eq.mp (congrArg (fun r => F.object.rowVolume z u.val r) he.symm) hF.1

theorem GammaMeasuredRVSchema.presentedRow_density
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma))
    (c : (volumeGammaSpace hc).domain)
    (hCode : (volumeGammaSpace hc).decode c = (F.presentedRowForm z hz P u).val) :
    F.rowDensity z u.val c :=
  (F.rowGammaValue_graph z hz (F.presentedRowLabels z hz P u) c).mpr hCode

end DiamondIntegral.Section3
