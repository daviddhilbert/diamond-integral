import «section 3».GammaMeasuredNormalizationRows

/-! Any actual presentation of a valid raw measured row carries its
complete Gamma form. The subsequent normalization is precisely the
essential schema row, without discarding the raw zero fibre early. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}
variable (F : GammaMeasuredRVSchema hc B p a (k+1) sp) (z : Fin p → M) (hF : F.valid z)
variable (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1)
  (F.object.rowDomain z) (F.object.rowVolume z))

def GammaMeasuredRVSchema.rawRowLabels :
    GammaGroundMap (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) (F.rowDomain z) :=
  GammaGroundMap.inclusion (fun r hr => P.domain_eq.le ((Section5.nativeRVGroundDomain_carrier _).le hr))

def GammaMeasuredRVSchema.rawRowForm :
    GammaGroundVolumeForm hc ⟨B.real ∪ Set.range z,B.gamma⟩
      (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :=
  (F.rowForm z hF).comp (F.rawRowLabels z P)

include hF in
theorem GammaMeasuredRVSchema.rawRow_volume (x : Fin a → RV (M := M)) (y : Fin (k+1) → RV (M := M)) :
    F.object.rowVolume z x y ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma),
        u.val = x ∧ (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) u).val = y := by
  constructor
  · intro hxy
    obtain ⟨v,hv,hvy⟩ := (P.graph_iff x y).mpr ⟨F.object.valid_row_support hF.1 x y hxy,hxy⟩
    let u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma) :=
      ⟨v.val,(Section5.nativeRVGroundDomain_carrier _).ge v.property⟩
    refine ⟨u,hv,?_⟩
    rw [gammaNativeRVGroundVolume_value]
    exact hvy
  · rintro ⟨u,hu,hy⟩
    let v : P.domain := ⟨u.val,(Section5.nativeRVGroundDomain_carrier _).le u.property⟩
    have hv : (P.volume v).val = y := by
      rw [gammaNativeRVGroundVolume_value] at hy
      exact hy
    exact ((P.graph_iff x y).mp ⟨v,hu,hv⟩).2

theorem GammaMeasuredRVSchema.rawRow_density (x : Fin a → RV (M := M)) (c : (volumeGammaSpace hc).domain) :
    F.rowDensity z x c ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma),
        u.val = x ∧ (F.rawRowForm z hF P u).val = (volumeGammaSpace hc).decode c := by
  constructor
  · intro hd
    have hx := F.rowDensity_support z hF x c hd
    let u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma) :=
      ⟨x,(Section5.nativeRVGroundDomain_carrier _).ge (P.domain_eq.ge hx)⟩
    refine ⟨u,rfl,?_⟩
    exact ((F.rowGammaValue_graph z hF (F.rawRowLabels z P u) c).mp hd).symm
  · rintro ⟨u,rfl,hw⟩
    exact (F.rowGammaValue_graph z hF (F.rawRowLabels z P u) c).mpr hw.symm

theorem GammaMeasuredRVSchema.rawRow_normalization :
    GammaMeasuredObjectRow z
      (gammaNativeMeasuredNormalization (gammaUniversalObject P.toGamma) (F.rawRowForm z hF P)) F.essential :=
  gammaMeasured_normalization_row z (gammaUniversalObject P.toGamma) (F.rawRowForm z hF P) F
    (F.rawRow_volume z hF P) (F.rawRow_density z hF P)

end DiamondIntegral.Section3
