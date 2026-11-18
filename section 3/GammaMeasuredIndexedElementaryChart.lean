import «section 3».GammaMeasuredIndexedWeights
import «section 3».GammaIndexedElementaryCharts
import «section 3».GammaNativeMeasuredIsomorphisms
import «section 3».GammaUniversalIsomorphismMaps
import «section 3».GammaMeasuredSchemaOperationValidity

/-! The existing indexed elementary reassociation carries the complete
Gamma density back to the old labels and preserves the full volume tuple. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.vfSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaMeasuredRVSchema.indexedElementaryChart {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ)
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv)) (A N : ℕ)
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t))
    (hAd : ∀ t ∈ T, (GammaFiniteAdmissibilitySchema.mk F.object (Fin.last k) A).valid (rvValues t))
    (hE : ∀ t ∈ T, (F.elementaryFormula.withBound N).valid (rvValues t))
    (P : F.object.IndexedPresentation BP)
    (Q : (F.elementaryFormula.withBound N).object.IndexedPresentation BP) :
    let U := gammaUniversalObject P.toGamma
    let Ad : GammaFiniteAdmissibilitySchema B p a (k+1) (fun _ => .rv) := ⟨F.object,Fin.last k,A⟩
    let hAP := gammaUniversalObject_admissible P.toGamma (Ad.indexed_admissible BP hAd P)
    Nonempty (GammaGroundMeasuredRVHom
      ((F.elementaryFormula.withBound N).indexedObject BP hE Q)
      (gammaNativeMeasuredNormalization (gammaElementaryAt hκ hs h00 hr U (Fin.natAdd d (Fin.last k)) hAP)
        ((F.indexedForm BP hF P).comp
          (gammaNativeElementaryOldLabel hκ hs h00 hr U (Fin.natAdd d (Fin.last k)) hAP)))) := by
  intro U Ad hAP
  let ER := F.elementaryFormula.withBound N
  let V := gammaElementaryAt hκ hs h00 hr U (Fin.natAdd d (Fin.last k)) hAP
  let D := gammaFiniteElementaryBasic hκ hs h00 hr P.toGamma (Fin.natAdd d (Fin.last k))
    (Ad.indexed_admissible BP hAd P)
  let e := Ad.indexedElementaryIso hκ hs h00 hr BP hAd P Q
  let E : GammaIsoAt (gammaUniversalObject Q.toGamma) V := gammaUniversalIsoAt Q.toGamma D e
  let ω := F.indexedForm BP hF P
  let Ψ := ER.indexedForm BP hE Q
  let π := ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U (Fin.natAdd d (Fin.last k)) hAP)
  refine ⟨gammaNativeMeasuredNormalizationHom Ψ π E (fun u => ?_)⟩
  let v := (Section5.nativeRVGroundIso E).map u
  let u0 := Section5.nativeRVGroundDomainEquiv (gammaUniversalObject Q.toGamma) u
  let w : Fin (p+(a+1)) → RV (M := M) := u.val
  have hMapRaw : (e.equiv u0).val = indexedElementaryLabels w :=
    gammaIndexedElementaryIso_labels hκ hs h00 hr Ad BP hAd P Q u0
  have hMap : v.val = indexedElementaryLabels u.val :=
    (gammaUniversalIsoAt_map Q.toGamma D e u).trans hMapRaw
  let b := gammaNativeElementaryOldLabel hκ hs h00 hr U (Fin.natAdd d (Fin.last k)) hAP v
  have hOld : b.val = Fin.append (indexedLeft u.val) (indexedRight u.val ∘ Fin.castAdd 1) := by
    rw [gammaNativeElementaryOldLabel_val,hMap,indexedElementaryLabels_head]
  have hu := ER.indexed_mem BP Q u
  have hFinE := ER.object.finiteRow_of_valid _ (hE _ hu.1).1
  have hRow := F.object.rowValue_elementary (rvValues (indexedLeft w)) (fun j => (indexedLeft w j).property) (Fin.last k)
    (F.object.finiteRow_of_valid _ (hF _ hu.1).1) hFinE (indexedRight w) hu.2
  have hTarget := F.object.indexed_elementary_volume BP P (Fin.last k) w (e.equiv u0) hMapRaw
  have hVolume : (Section5.nativeRVGroundVolume (gammaUniversalObject Q.toGamma) u).val =
      (Section5.nativeRVGroundVolume V v).val := by
    have hTargetNative : (Section5.nativeRVGroundVolume V v).val =
        Fin.append (BP.totalVolume (indexedLeft w))
          (@blowupValue M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (k+1) (Fin.last k)
            (F.object.rowValue (rvValues (indexedLeft w)) (indexedRight w ∘ Fin.castAdd 1))
            (indexedRight w (Fin.natAdd a 0))) := by
      rw [gammaNativeRVGroundVolume_value]
      exact hTarget
    exact (ER.indexed_volume BP Q u).trans
      ((congrArg (Fin.append (BP.totalVolume (indexedLeft w))) hRow).trans hTargetNative.symm)
  obtain ⟨c,hcValue⟩ := (volumeGammaSpace hc).onto (Ψ u).val
  have hDensity := ER.indexed_density BP hE Q u c hcValue
  have hDensityOld := ((F.elementary_rowDensity _ (hF _ hu.1).1.1 (indexedRight u.val) c).mp hDensity).1
  have hb := F.indexed_mem BP P b
  have hC : F.rowDensity (rvValues (indexedLeft b.val)) (indexedRight b.val) c := by
    rw [hOld]
    simpa only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right] using hDensityOld
  have hForm : (Ψ u).val = (ω b).val :=
    hcValue.symm.trans ((F.rowGammaValue_graph _ (hF _ hb.1) ⟨indexedRight b.val,hb.2⟩ c).mp hC)
  have hDensityValue : gammaGroundFormValue Ψ u = gammaGroundFormValue π v :=
    congrArg (cast (gammaCarrier hc)) hForm
  unfold gammaNativeCombinedWeight
  rw [hVolume,hDensityValue]

end DiamondIntegral.Section3
