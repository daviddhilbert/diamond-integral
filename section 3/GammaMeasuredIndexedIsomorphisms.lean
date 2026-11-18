import «section 3».GammaMeasuredIndexedWeights
import «section 3».GammaMeasuredChartProducts
import «section 3».GammaMeasuredEssentialSchemata
import «section 3».GammaUniversalIsomorphismMaps
import «section 3».GammaNativeMeasuredIsomorphisms
import IntegrationSection6.GammaSchemaIndexedCharts

/-! Measured chart assembly over an actual finite-volume RV index.
The original index is retained and contributes the same weight on both
sides; the fibre density is interpreted in Gamma throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaMeasuredRVIsoSchema.indexedRealize
    (I : GammaMeasuredRVIsoSchema hc B p a b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hI : ∀ t ∈ T, I.valid (rvValues t))
    (P : I.source.essential.object.IndexedPresentation BP)
    (Q : I.target.essential.object.IndexedPresentation BP) :
    Nonempty (GammaGroundMeasuredRVHom
      (I.source.essential.indexedObject BP (fun t ht => I.source.essential_valid _ (hI t ht).1) P)
      (I.target.essential.indexedObject BP (fun t ht => I.target.essential_valid _ (hI t ht).2.1) Q)) := by
  let hF := fun t ht => I.source.essential_valid (rvValues t) (hI t ht).1
  let hG := fun t ht => I.target.essential_valid (rvValues t) (hI t ht).2.1
  let e := I.ordinary.indexedIso BP (fun t ht => (hI t ht).2.2.1) P Q
  let E := gammaUniversalIsoAt P.toGamma Q.toGamma e
  let ω := I.source.essential.indexedForm BP hF P
  let η := I.target.essential.indexedForm BP hG Q
  refine ⟨gammaNativeMeasuredNormalizationHom ω η E (fun u => ?_)⟩
  let v := (Section5.nativeRVGroundIso E).map u
  let w := P.domainEquiv (Section5.nativeRVGroundDomainEquiv (gammaUniversalObject P.toGamma) u)
  have hLeft : indexedLeft v.val = indexedLeft u.val :=
    indexedEquiv_left T (fun t => I.ordinary.source.rowDomain (rvValues t))
      (fun t => I.ordinary.target.rowDomain (rvValues t))
      (fun t => I.ordinary.rowEquiv (rvValues t.val) ((hI t.val t.property).2.2.1)) w
  have hRight : indexedRight v.val =
      (I.ordinary.rowEquiv (rvValues (indexedLeft u.val)) ((hI _ w.property.1).2.2.1)
        ⟨indexedRight u.val,w.property.2⟩).val :=
    indexedEquiv_right T (fun t => I.ordinary.source.rowDomain (rvValues t))
      (fun t => I.ordinary.target.rowDomain (rvValues t))
      (fun t => I.ordinary.rowEquiv (rvValues t.val) ((hI t.val t.property).2.2.1)) w
  have hChart : Fin.append (Fin.append (rvValues (indexedLeft u.val)) (rvValues (indexedRight u.val)))
      (rvValues (indexedRight v.val)) ∈ I.chart := by
    rw [hRight]
    exact I.ordinary.rowEquiv_apply _ ((hI _ w.property.1).2.2.1) ⟨indexedRight u.val,w.property.2⟩
  let z := rvValues (indexedLeft u.val)
  let α := I.source.essential.object.rowValue z (indexedRight u.val)
  let β := I.target.essential.object.rowValue (rvValues (indexedLeft v.val)) (indexedRight v.val)
  have hα : I.source.object.rowVolume z (indexedRight u.val) α :=
    ((essentialFiniteVolumeSchema_rowVolume I.source.object z _ α).mp
      ((I.source.essential.object.rowValue_graph z (hF _ w.property.1).1 _ w.property.2 α).mpr rfl)).1
  have hV := I.target.essential.indexed_mem BP Q v
  have hβ : I.target.object.rowVolume z (indexedRight v.val) β := by
    have h := ((essentialFiniteVolumeSchema_rowVolume I.target.object _ _ β).mp
      ((I.target.essential.object.rowValue_graph _ (hG _ hV.1).1 _ hV.2 β).mpr rfl)).1
    simpa only [hLeft] using h
  obtain ⟨c,hcVal⟩ := (volumeGammaSpace hc).onto (ω u).val
  obtain ⟨f,hfVal⟩ := (volumeGammaSpace hc).onto (η v).val
  have hC : I.source.rowDensity z (indexedRight u.val) c :=
    ((I.source.essential_rowDensity z (indexedRight u.val) c).mp
      (I.source.essential.indexed_density BP hF P u c hcVal)).1
  have hF' : I.target.rowDensity z (indexedRight v.val) f := by
    have h := ((I.target.essential_rowDensity _ (indexedRight v.val) f).mp
      (I.target.essential.indexed_density BP hG Q v f hfVal)).1
    simpa only [hLeft] using h
  have hBalance := I.chart_product z (hI _ w.property.1) (indexedRight u.val) (indexedRight v.val)
    α β c f hα hβ hC hF' hChart
  rw [gammaMeasuredCodeProduct ω u α c hcVal,gammaMeasuredCodeProduct η v β f hfVal] at hBalance
  rw [I.source.essential.indexed_weight BP hF P u,I.target.essential.indexed_weight BP hG Q v]
  change (∏ j, Values.vrv (BP.totalVolume (indexedLeft u.val) j)) * _ =
    (∏ j, Values.vrv (BP.totalVolume (indexedLeft v.val) j)) * _
  rw [hLeft]
  apply congrArg (fun q => (∏ j, Values.vrv (BP.totalVolume (indexedLeft u.val) j)) * q)
  simpa only [ω,η,α,β,z,hLeft] using hBalance

end DiamondIntegral.Section3
