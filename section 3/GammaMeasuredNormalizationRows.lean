import «section 3».GammaMeasuredObjectRows
import «section 3».GammaMeasuredEssentialSchemata
import «section 3».GammaMeasuredRowPresentations

/-! Literal normalization of a native measured RV row is exactly the
essential part of its complete measured schema. The entire structural
volume tuple and every Gamma representative are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gammaNativeHighLabel_volume (U : GammaObjectAt B Set.univ (k+1))
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)) :
    (Section5.nativeRVGroundVolume U (gammaNativeHighLabelInclusion U u)).val =
      (Section5.nativeRVGroundVolume (gammaHighRestrictionAt U) u).val := by
  rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
  rfl

theorem gammaNativeHigh_domain_nonzero (U : GammaObjectAt B Set.univ (k+1))
    (x : Fin (rvObjectArity U.object.obj) → RV (M := M)) :
    x ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)).carrier ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) U, u.val = x ∧
        ∀ i, ((Section5.nativeRVGroundVolume U u).val i).val ≠ iRVZero := by
  constructor
  · intro hx
    let v : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U) := ⟨x,hx⟩
    refine ⟨gammaNativeHighLabelInclusion U v,rfl,?_⟩
    intro i
    rw [gammaNativeHighLabel_volume]
    exact (Section5.nativeRVGroundObject (gammaHighRestrictionAt U) (gammaHighRestriction_fullWeight U)).nonzero v i
  · rintro ⟨u,rfl,hn⟩
    apply (Section5.nativeRVGroundDomain_carrier (gammaHighRestrictionAt U)).ge
    let a := Section5.nativeRVGroundDomainEquiv (hc := hc) U u
    refine ⟨a.property,?_⟩
    intro hl
    obtain ⟨j,hj⟩ := (@rvWeight_le_pred_iff_zero M N k (rvObjectVolume U.object.obj a).val).mp
      ((@mem_rvLowDomain M N Set.univ k U.object.obj a).mp hl)
    apply hn j
    rw [gammaNativeRVGroundVolume_value]
    exact hj.trans (CanonicalStructure.sortZero_normalize .rv)

theorem gammaMeasured_normalization_row
    (z : Fin p → M) (U : GammaObjectAt ⟨B.real ∪ Set.range z,B.gamma⟩ Set.univ (k+1))
    (ω : GammaGroundVolumeForm hc ⟨B.real ∪ Set.range z,B.gamma⟩ (Section5.nativeRVGroundDomain U))
    (F : GammaMeasuredRVSchema hc B p (rvObjectArity U.object.obj) (k+1) sp)
    (hVol : ∀ x y, F.object.rowVolume z x y ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) U, u.val = x ∧ (Section5.nativeRVGroundVolume U u).val = y)
    (hDensity : ∀ x c, F.rowDensity z x c ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) U, u.val = x ∧ (ω u).val = (volumeGammaSpace hc).decode c) :
    GammaMeasuredObjectRow z (gammaNativeMeasuredNormalization U ω) F.essential := by
  let W := gammaNativeMeasuredNormalization U ω
  have hDomain (x) : x ∈ F.essential.object.rowDomain z ↔ x ∈ W.underlying.domain.carrier := by
    change x ∈ (essentialFiniteVolumeSchema F.object).rowDomain z ↔
      x ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)).carrier
    rw [essentialFiniteVolumeSchema_rowDomain,gammaNativeHigh_domain_nonzero]
    constructor
    · rintro ⟨v,hv,hn⟩
      obtain ⟨u,hu,hVolu⟩ := (hVol x v).mp hv
      exact ⟨u,hu,fun i => congrArg (fun t => (t i).val) hVolu ▸ hn i⟩
    · rintro ⟨u,hu,hn⟩
      exact ⟨(Section5.nativeRVGroundVolume U u).val,(hVol x _).mpr ⟨u,hu,rfl⟩,hn⟩
  have hVolume (x y) : F.essential.object.rowVolume z x y ↔
      ∃ u : W.underlying.domain, u.val = x ∧ (W.underlying.volume u).val = y := by
    change (essentialFiniteVolumeSchema F.object).rowVolume z x y ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U),
        u.val = x ∧ (Section5.nativeRVGroundVolume (gammaHighRestrictionAt U) u).val = y
    rw [essentialFiniteVolumeSchema_rowVolume]
    constructor
    · rintro ⟨hv,hn⟩
      obtain ⟨u,hu,hVu⟩ := (hVol x y).mp hv
      have hD := (gammaNativeHigh_domain_nonzero U x).mpr ⟨u,hu,fun i => congrArg (fun t => (t i).val) hVu ▸ hn i⟩
      let q : W.underlying.domain := ⟨x,hD⟩
      have he : gammaNativeHighLabelInclusion U q = u := Subtype.ext hu.symm
      refine ⟨q,rfl,?_⟩
      exact (gammaNativeHighLabel_volume U q).symm.trans ((congrArg (fun u => (Section5.nativeRVGroundVolume U u).val) he).trans hVu)
    · rintro ⟨u,rfl,hv⟩
      refine ⟨(hVol u.val y).mpr ⟨gammaNativeHighLabelInclusion U u,rfl,(gammaNativeHighLabel_volume U u).trans hv⟩,?_⟩
      intro i
      exact congrArg (fun t => (t i).val) hv ▸ W.underlying.nonzero u i
  refine ⟨Set.ext hDomain,hVolume,?_⟩
  intro x c
  rw [F.essential_rowDensity]
  constructor
  · rintro ⟨hd,hx⟩
    obtain ⟨u,hu,hω⟩ := (hDensity x c).mp hd
    let q : W.underlying.domain := ⟨x,(hDomain x).mp hx⟩
    have he : gammaNativeHighLabelInclusion U q = u := Subtype.ext hu.symm
    exact ⟨q,rfl,(congrArg (fun u => (ω u).val) he).trans hω⟩
  · rintro ⟨u,rfl,hω⟩
    exact ⟨(hDensity u.val c).mpr ⟨gammaNativeHighLabelInclusion U u,rfl,hω⟩,(hDomain u.val).mpr u.property⟩

end DiamondIntegral.Section3
