import «section 3».GammaNativeUnarySpecialComparison
import «section 3».GammaNativePreparedConjugacy
import «section 3».GammaUnaryRVFullKeyComparison
import IntegrationSection5.UnaryBijectionPreparation

/-! Full measured unary VF bijections have equal classes in the stated
principal Gamma quotient. Both preparations, their exact densities and
the actual terminal RV isomorphism are constructed here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativeUnaryFullMeasured_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (FBase : VFFieldBase B.real)
    (U V : GammaObjectAt B Set.univ 1)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η)) :
    gammaNativeSpecialClass U ω = gammaNativeSpecialClass V η := by
  let f0 := gammaNativeTypedMeasuredMap hκ.le hs hr hv U V ω η f
  have hf0 := gammaNativeTypedMeasuredMap_bijective hκ.le hs hr hv U V ω η f
  obtain ⟨R,hSR,r,s,C,D,TU,TV,hTU,hTV,hC,hD,hContract,hback,hgraph,_⟩ :=
    IntegrationInACVF.Section5.lemma_5_2_gamma_presented hκ.le hs hr h00 δ hδ hδ1 FBase (Set.subset_univ _)
      f0 hf0 (gammaNativeTypedLift_definable U) (gammaNativeTypedLift_definable V)
      (gammaNativeTypedMeasuredMap_graph hκ.le hs hr hv U V ω η f)
  have hR : R = Set.univ := Set.eq_univ_of_univ_subset hSR
  subst R
  let g := IntegrationInACVF.Section5.unaryConjugate TU TV f0
  have hg := IntegrationInACVF.Section5.unaryConjugate_bijective TU TV f0 hf0
  obtain ⟨e,he,heΓ,_⟩ := IntegrationInACVF.Section5.lemma_5_3 hκ.le hs hr g hg hContract hback hC hD hgraph
  obtain ⟨hCF,HU⟩ := gammaNativeUnarySpecial_comparison hκ.le hs h00 hr U
    (normalizedTypedLift_presents U.object.obj) TU hTU ω
  obtain ⟨hDF,HV⟩ := gammaNativeUnarySpecial_comparison hκ.le hs h00 hr V
    (normalizedTypedLift_presents V.object.obj) TV hTV η
  let PC := gammaPullbackAt (Set.subset_univ _) C (GammaChainDefinable.target B TU.chain hTU) hCF
  let PD := gammaPullbackAt (Set.subset_univ _) D (GammaChainDefinable.target B TV.chain hTV) hDF
  let ωC := ω.comp (gammaPreparedRVLabelMap (hc := hc) U (normalizedTypedLift_presents U.object.obj) TU hTU hCF)
  let ηD := η.comp (gammaPreparedRVLabelMap (hc := hc) V (normalizedTypedLift_presents V.object.obj) TV hTV hDF)
  let E : GammaIsoAt PC PD := GammaIsoAt.ofAmbient e heΓ
  have hSpec := gammaUnaryRV_full_key_comparison (hc := hc) U V TU TV hTU hTV hCF hDF f0 e he heΓ
  let F := gammaNativePreparedFullConjugate hκ.le hs hr hv U V ω η f TU TV hTU hTV hC hD hCF hDF
  have hLabel := gammaNativePreparedConjugate_label hκ.le hs hr hv U V ω η f
    TU TV hTU hTV hC hD hCF hDF E hSpec
  let H := gammaNativeFullLabelMeasuredHom hκ hs h00 hr hv PC PD ωC ηD E F hLabel
  exact HU.trans ((gammaNativeSpecialClass_hom PC PD ωC ηD H).trans HV.symm)

end DiamondIntegral.Section3
