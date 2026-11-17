import «section 3».GammaMeasuredIndexedWeights
import «section 3».GammaPresentationIdentityCharts
import «section 3».GammaNativeMeasuredIsomorphisms
import IntegrationSection6.GammaSchemaIndexedEquality
import Integration7.GammaVolumeSchemaRowEquality

/-! Exact domain, volume and complete density rows give a measured
indexed isomorphism by identity on all the original labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaMeasuredRVSchema.indexedAgreement
    (F G : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
    (hEq : ∀ t ∈ T, F.toRVTemplate.sameRow G.toRVTemplate (rvValues t))
    (P : F.object.IndexedPresentation BP) (Q : G.object.IndexedPresentation BP) :
    Nonempty (GammaGroundMeasuredRVHom (F.indexedObject BP hF P) (G.indexedObject BP hG Q)) := by
  have hD : indexedDomain T (fun t => F.object.rowDomain (rvValues t)) =
      indexedDomain T (fun t => G.object.rowDomain (rvValues t)) := by
    ext w
    constructor
    · rintro ⟨ht,hx⟩
      exact ⟨ht,((hEq _ ht).1.2.1 (rvValues (indexedRight w))).mp hx⟩
    · rintro ⟨ht,hx⟩
      exact ⟨ht,((hEq _ ht).1.2.1 (rvValues (indexedRight w))).mpr hx⟩
  have hR : ∀ w y,
      (w ∈ indexedDomain T (fun t => F.object.rowDomain (rvValues t)) ∧
        indexedVolume BP.totalVolume (fun t => F.object.rowValue (rvValues t)) w = y) ↔
      (w ∈ indexedDomain T (fun t => G.object.rowDomain (rvValues t)) ∧
        indexedVolume BP.totalVolume (fun t => G.object.rowValue (rvValues t)) w = y) := by
    intro w y
    by_cases ht : indexedLeft w ∈ T
    · have hValue := F.object.rowValue_eq_of_sameRow G.object _ (hEq _ ht).1
      have hV : indexedVolume BP.totalVolume (fun t => F.object.rowValue (rvValues t)) w =
          indexedVolume BP.totalVolume (fun t => G.object.rowValue (rvValues t)) w :=
        congrArg (fun v => Fin.append (BP.totalVolume (indexedLeft w)) v)
          (congrFun hValue (indexedRight w))
      rw [hD,hV]
    · exact ⟨fun h => False.elim (ht h.1.1),fun h => False.elim (ht h.1.1)⟩
  let e := gammaPresentationIdentityIso P Q hD hR
  let E := gammaUniversalIsoAt P.toGamma Q.toGamma e
  let ω := F.indexedForm BP hF P
  let η := G.indexedForm BP hG Q
  refine ⟨gammaNativeMeasuredNormalizationHom ω η E (fun u => ?_)⟩
  let v := (Section5.nativeRVGroundIso E).map u
  have hv : v.val = u.val :=
    gammaPresentationIdentityIso_labels P Q hD hR
      (Section5.nativeRVGroundDomainEquiv (gammaUniversalObject P.toGamma) u)
  have hu := F.indexed_mem BP P u
  have hVolume := F.object.rowValue_eq_of_sameRow G.object _ (hEq _ hu.1).1
  obtain ⟨c,hcVal⟩ := (volumeGammaSpace hc).onto (ω u).val
  have hFC := F.indexed_density BP hF P u c hcVal
  have hGC : G.rowDensity (rvValues (indexedLeft v.val)) (indexedRight v.val) c := by
    rw [hv]
    exact ((hEq _ hu.1).2.2.2 (rvValues (indexedRight u.val)) c.val).mp hFC
  have hValue : (η v).val = (ω u).val := by
    exact ((G.rowGammaValue_graph _ (hG _ (G.indexed_mem BP Q v).1)
      ⟨indexedRight v.val,(G.indexed_mem BP Q v).2⟩ c).mp hGC).symm.trans hcVal
  have hForm : gammaGroundFormValue η v = gammaGroundFormValue ω u :=
    congrArg (cast (gammaCarrier hc)) hValue
  rw [F.indexed_weight BP hF P u,G.indexed_weight BP hG Q v]
  change (∏ j, Values.vrv (BP.totalVolume (indexedLeft u.val) j)) * _ =
    (∏ j, Values.vrv (BP.totalVolume (indexedLeft v.val) j)) * _
  rw [hv,hForm]
  exact congrArg (fun q => (∏ j, Values.vrv (BP.totalVolume (indexedLeft u.val) j)) *
    ((gammaGroundFormValue ω u).val * ∏ j, Values.vrv (q j))) (congrFun hVolume (indexedRight u.val))

end DiamondIntegral.Section3
