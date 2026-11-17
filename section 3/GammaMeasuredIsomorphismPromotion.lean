import «section 3».GammaMeasuredWeightedRowValues
import «section 3».GammaMeasuredChartWeightValidity
import «section 3».GammaNativeFullGroundIsomorphisms
import Integration7.GammaFiniteRowIsomorphismWitnesses

/-! Full Gamma-measured row bijections have genuine original-base chart
witnesses. Object and chart promotion are the existing native theorems;
the measured check uses every representative of the two Gamma forms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p k : ℕ} {sp : Fin p → SortTag}

theorem gammaMeasured_isomorphism_schema_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (z : Fin p → M)
    (U V : GammaObjectAt ⟨B.real ∪ Set.range z,B.gamma⟩ Set.univ (k+1))
    (hU : GammaFullWeightAt U) (hV : GammaFullWeightAt V)
    (ω : GammaGroundVolumeForm hc ⟨B.real ∪ Set.range z,B.gamma⟩ (Section5.nativeRVGroundDomain U))
    (π : GammaGroundVolumeForm hc ⟨B.real ∪ Set.range z,B.gamma⟩ (Section5.nativeRVGroundDomain V))
    (F : GammaMeasuredRVSchema hc B p (rvObjectArity U.object.obj) (k+1) sp)
    (G : GammaMeasuredRVSchema hc B p (rvObjectArity V.object.obj) (k+1) sp)
    (hF : F.valid z) (hG : G.valid z)
    (hRF : gammaSchemaRepresents U.toGamma F.object z)
    (hRG : gammaSchemaRepresents V.toGamma G.object z)
    (hDF : ∀ x y, Fin.append (Fin.append z x) y ∈ F.density ↔ Fin.append x y ∈ gammaRVFormCodeRows ω)
    (hDG : ∀ x y, Fin.append (Fin.append z x) y ∈ G.density ↔ Fin.append x y ∈ gammaRVFormCodeRows π)
    (f : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain V))
    (hf : ∀ u, gammaNativeCombinedWeight U ω u = gammaNativeCombinedWeight V π (f.map u)) :
    ∃ I : GammaMeasuredRVIsoSchema hc B p (rvObjectArity U.object.obj) (rvObjectArity V.object.obj) k sp,
      I.source = F ∧ I.target = G ∧ I.valid z ∧
      (∀ x y, Fin.append (Fin.append z x) y ∈ I.chart ↔
        ∃ u : Section5.nativeRVGroundDomain (hc := hc) U, rvValues u.val = x ∧ rvValues (f.map u).val = y) := by
  let e := gammaNativeFullGroundIso U V hU hV f
  obtain ⟨W,hW,hSD,hSV,hTD,hTV,hChart⟩ := gamma_sorted_finite_isomorphism_promotion
    hκ hs hr hg sp z hF.1.1 U.toGamma V.toGamma e.toGamma
  let I : GammaMeasuredRVIsoSchema hc B p (rvObjectArity U.object.obj) (rvObjectArity V.object.obj) k sp :=
    ⟨F,G,W.chart,W.chart_definable⟩
  have hRE := gammaSchemaRepresents_essential_of_full U hU F.object z hRF
  have hSE := gammaSchemaRepresents_essential_of_full V hV G.object z hRG
  have hOrd : I.ordinary.valid z := gamma_finite_row_chart_valid_of_rows W
    (essentialFiniteVolumeSchema F.object) (essentialFiniteVolumeSchema G.object) z hW
    (essentialFiniteVolumeSchema_valid F.object z hF.1) (essentialFiniteVolumeSchema_valid G.object z hG.1)
    ⟨fun x => (hSD x).trans (hRE.1 x).symm,fun x y => (hSV x y).trans (hRE.2 x y).symm⟩
    ⟨fun x => (hTD x).trans (hSE.1 x).symm,fun x y => (hTV x y).trans (hSE.2 x y).symm⟩
  have hMap (u : Section5.nativeRVGroundDomain (hc := hc) U) :
      (e.toGamma.equiv (Section5.nativeRVGroundDomainEquiv U u)).val = (f.map u).val :=
    congrArg Subtype.val (gammaNativeFullGroundIso_map U V hU hV f u)
  have hActualChart (x y) : Fin.append (Fin.append z x) y ∈ I.chart ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) U, rvValues u.val = x ∧ rvValues (f.map u).val = y := by
    rw [show I.chart = W.chart from rfl,hChart,gammaRawIsoGraph_append_iff]
    constructor
    · rintro ⟨a,ha,hb⟩
      let u := (Section5.nativeRVGroundDomainEquiv (hc := hc) U).symm a
      refine ⟨u,ha,?_⟩
      have he := hMap u
      have hau : Section5.nativeRVGroundDomainEquiv U u = a := (Section5.nativeRVGroundDomainEquiv U).apply_symm_apply a
      rw [hau] at he
      exact funext (fun j => (congrArg (fun t => (t j).val) he).symm.trans (congrFun hb j))
    · rintro ⟨u,hu,hv⟩
      refine ⟨Section5.nativeRVGroundDomainEquiv U u,hu,?_⟩
      exact funext (fun j => (congrArg (fun t => (t j).val) (hMap u)).trans (congrFun hv j))
  have hWeight : volumeChartGammaRowValid F.toRVTemplate G.toRVTemplate I.chart z := by
    apply gamma_volumeChartGammaRowValid_of_typed F.toRVTemplate G.toRVTemplate I.chart_definable z hF.1.1
    intro x y μ ν hμ hxy hν
    obtain ⟨u,hu,hμNZ,hμVal⟩ := gammaMeasured_weighted_row_value z U hU ω F hRF hDF x μ hμ
    obtain ⟨v,hv,hνNZ,hνVal⟩ := gammaMeasured_weighted_row_value z V hV π G hRG hDG y ν hν
    obtain ⟨a,ha,hfa⟩ := (hActualChart x y).mp hxy
    have hau : a = u := Subtype.ext (rvValues_injective (ha.trans hu.symm))
    subst a
    have hfv : f.map u = v := Subtype.ext (rvValues_injective (hfa.trans hv.symm))
    apply (rvProductGammaBalance_append ((k+1)+1) μ ν).mpr
    refine ⟨hμNZ,hνNZ,?_⟩
    rw [hμVal,hνVal]
    exact (hf u).trans (congrArg (gammaNativeCombinedWeight V π) hfv)
  exact ⟨I,rfl,rfl,⟨hF,hG,hOrd,hWeight⟩,hActualChart⟩

end DiamondIntegral.Section3
