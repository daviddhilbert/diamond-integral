import «section 3».GammaGroundRVGenerators
import «section 4».Section3RVChartRingMaps
import «section 4».RVOrdinaryPNormalization

/-! The native Section 3 principal lifting relation maps to the actual
Section 4 chart relation P=1. The point and positive ray are identified by
original-ground full-domain identity graphs, without any HK input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge Section3RVClassCuts GammaRVLifts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))

theorem nativePoint_raw_domain :
    (Section3RVChartBridge.chart (GammaGroundRVObject.ofReal (hc := hc) (ground := B)
      (rvOneObject B.real))).domain = (RESFibreObjects.point B).domain := by
  ext z
  change z ∈ rvValues '' (rvOneDomain B.real).carrier ↔ z ∈ ({![(1 : CanonicalRV.RVSort M).val]} : Set (Fin 1 → M))
  rw [RVOperations.one_val]
  constructor
  · rintro ⟨a,⟨u,hu⟩,he⟩
    rw [←he,←hu]
    apply funext
    intro i
    fin_cases i
    rfl
  · intro hz
    have hz' : z = ![iRVOne] := hz
    subst z
    let u : (RVObject.unit (M := M) B.real).domain := ⟨Fin.elim0,Set.mem_univ _⟩
    refine ⟨((rvRightTagMap (RVObject.unit B.real).domain 0) u).val,⟨u,rfl⟩,?_⟩
    funext i
    fin_cases i
    rfl

theorem nativeCodeValue_one : codeValue (iRVOne : M) = 1 := by
  have h : codeValue (1 : CanonicalRV.RVSort M).val = 1 := GammaRVLifts.valueHom.map_one
  simpa only [RVOperations.one_val] using h

theorem nativeOne_nonzero : NonzeroRV (iRVOne : M) := by
  have h := unit_nonzero_code (1 : (CanonicalRV.RVSort M)ˣ)
  change NonzeroRV (1 : CanonicalRV.RVSort M).val at h
  simpa only [RVOperations.one_val] using h

theorem nativePositive_raw_domain :
    (Section3RVChartBridge.chart (GammaGroundRVObject.ofReal (hc := hc) (ground := B)
      (rvPositiveObject hc B.real))).domain =
      (RVSharpCharts.sharpChart (RVMeasuredSpecialClasses.rayChart B)).domain := by
  ext z
  change Fin 1 → M at z
  change z ∈ rvValues '' (rvPositiveDomain hc B.real).carrier ↔
    Proper (z : Fin 1 → M) ∧ 1 < codeValue (z (0 : Fin 1))
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨?_,?_⟩
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨(a 0).property,ha.1⟩
    · have ht := (EndpointLogic.codeLt_iff iRVOne _ nativeOne_nonzero ⟨(a 0).property,ha.1⟩).mp ha.2
      change 1 < codeValue ((a (0 : Fin 1)).val)
      simpa only [nativeCodeValue_one] using ht
  · rintro ⟨hp,ht⟩
    let a : Fin 1 → CanonicalRV.RVSort M := fun i => ⟨z i,(hp i).1⟩
    refine ⟨a,⟨(hp 0).2,?_⟩,rfl⟩
    apply (EndpointLogic.codeLt_iff iRVOne _ nativeOne_nonzero (hp 0)).mpr
    simpa only [nativeCodeValue_one] using ht

def nativePointChartIso : RVForgetScissors.UnderlyingIso
    (Section3RVChartBridge.chart (GammaGroundRVObject.ofReal (hc := hc) (ground := B) (rvOneObject B.real)))
    (RESFibreObjects.point B).toChart :=
  RVForgetScissors.ofMap _ _ id
    (RVSharpCharts.identity_graph_definable B _ (rawDomain_definable (GammaGroundDefSet.ofReal (hc := hc) (ground := B) (rvOneDomain B.real))))
    (by rw [nativePoint_raw_domain]; exact Set.bijOn_id _)

def nativePositiveChartIso : RVForgetScissors.UnderlyingIso
    (Section3RVChartBridge.chart (GammaGroundRVObject.ofReal (hc := hc) (ground := B) (rvPositiveObject hc B.real)))
    (RVSharpCharts.sharpChart (RVMeasuredSpecialClasses.rayChart B)) :=
  RVForgetScissors.ofMap _ _ id
    (RVSharpCharts.identity_graph_definable B _ (rawDomain_definable (GammaGroundDefSet.ofReal (hc := hc) (ground := B) (rvPositiveDomain hc B.real))))
    (by rw [nativePositive_raw_domain]; exact Set.bijOn_id _)

theorem nativePrincipal_chart_class :
    Section3RVChartRingMaps.ordinary hc B (gammaGroundRVPrincipalElement hc B) =
      RVOrdinaryPNormalization.pClass B := by
  change Section3RVChartRingMaps.ordinary hc B
    (ordinaryClass (GammaGroundRVObject.ofReal (rvOneObject B.real)) -
      ordinaryClass (GammaGroundRVObject.ofReal (rvPositiveObject hc B.real))) = _
  rw [map_sub,Section3RVChartRingMaps.ordinary_class,Section3RVChartRingMaps.ordinary_class,
    RVOrdinaryRing.objectClass_iso (nativePointChartIso hc B),
    RVOrdinaryRing.objectClass_iso (nativePositiveChartIso hc B)]
  rfl

end DiamondIntegral.Section5
