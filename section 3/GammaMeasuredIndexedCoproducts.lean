import «section 3».GammaIndexedCoproductCharts
import «section 3».GammaMeasuredCoproductCodeRows
import «section 3».GammaMeasuredIndexedWeights
import «section 3».GammaNativeCoproductNormalization
import «section 3».GammaNativeMeasuredIsomorphisms
import «section 3».GammaUniversalIsomorphismMaps
import «section 3».GammaMeasuredGeometricSchemata

/-! Indexed assembly preserves measured coproducts. The native indexed
chart is reused with its full volume tuple and complete Gamma density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.vfSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaMeasuredRVSchema.indexedCoprodChart
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .rv)) (L : ℕ)
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
    (hK : ∀ t ∈ T, ((F.coprodFormula G).withBound L).valid (rvValues t))
    (P : F.object.IndexedPresentation BP) (Q : G.object.IndexedPresentation BP)
    (S : ((F.coprodFormula G).withBound L).object.IndexedPresentation BP) :
    Nonempty (GammaGroundMeasuredRVHom
      (((F.coprodFormula G).withBound L).indexedObject BP hK S)
      ((F.indexedObject BP hF P).coprod (G.indexedObject BP hG Q))) := by
  let U := gammaUniversalObject P.toGamma
  let V := gammaUniversalObject Q.toGamma
  let C := gammaCoprodAt U V
  let K := (F.coprodFormula G).withBound L
  let hFF := fun t ht => F.object.finiteRow_of_valid (rvValues t) (hF t ht).1
  let hGF := fun t ht => G.object.finiteRow_of_valid (rvValues t) (hG t ht).1
  let e := F.object.indexedCoprodIsoFromRows G.object BP hFF hGF P Q S
  let E : GammaIsoAt (gammaUniversalObject S.toGamma) C :=
    gammaUniversalIsoAt S.toGamma (P.coprod Q).toGamma e
  let ω := F.indexedForm BP hF P
  let η := G.indexedForm BP hG Q
  let δ := gammaNativeCoprodForm U V ω η
  let Ψ := K.indexedForm BP hK S
  have hWeight : ∀ u, gammaNativeCombinedWeight (gammaUniversalObject S.toGamma) Ψ u =
      gammaNativeCombinedWeight C δ ((Section5.nativeRVGroundIso E).map u) := by
    intro u
    let v := (Section5.nativeRVGroundIso E).map u
    let u0 := Section5.nativeRVGroundDomainEquiv (gammaUniversalObject S.toGamma) u
    obtain ⟨w,hw,hMap⟩ := gammaIndexedCoprodIso_labels F.object G.object BP hFF hGF P Q S u0
    have hMapNative : v.val =
        (indexedCoprodEquiv T (fun t => F.object.rowDomain (rvValues t))
          (fun t => G.object.rowDomain (rvValues t)) w).val :=
      (gammaUniversalIsoAt_map S.toGamma (P.coprod Q).toGamma e u).trans hMap
    have hVolume : (Section5.nativeRVGroundVolume (gammaUniversalObject S.toGamma) u).val =
        (Section5.nativeRVGroundVolume C v).val := by
      rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
      exact (gammaIndexedCoprodIso_volume F.object G.object BP hFF hGF P Q S u0).symm
    obtain ⟨c,hcValue⟩ := (volumeGammaSpace hc).onto (Ψ u).val
    have hDensity := K.indexed_density BP hK S u c hcValue
    let D := fun t => F.object.rowDomain (rvValues t)
    let A := fun t => G.object.rowDomain (rvValues t)
    have hForm : gammaGroundFormValue Ψ u = gammaGroundFormValue δ v := by
      rcases indexedCoprod_cases T D A w with ⟨t,x,he⟩|⟨t,x,he⟩
      · let px := (Section5.nativeRVGroundDomainEquiv (hc := hc) U).symm
          (P.domainEquiv.symm ((indexedSigmaEquiv T D).symm ⟨t,x⟩))
        have hu : u.val = Fin.append t.val (@rvLeftTag M N hN a b x.val) :=
          hw.symm.trans (congrArg Subtype.val he)
        have hImageRaw := hMapNative.trans
          ((congrArg (fun q => (indexedCoprodEquiv T D A q).val) he).trans (indexedCoprodEquiv_left T D A t x))
        have hImage : v.val = rvLeftTag (p+b) px.val := hImageRaw.trans
          (@Section5.rvLeftTag_normalized M sM hM (p+a) (p+b) (Fin.append t.val x.val))
        have hCode : F.rowDensity (rvValues t.val) x.val c := by
          apply (F.coprod_rowDensity_left G (rvValues t.val) (fun j => (t.val j).property) x.val c).mp
          have hd := hDensity
          change (F.coprodFormula G).rowDensity _ _ c at hd
          rw [hu] at hd
          simpa only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right] using hd
        have hpx := F.indexed_mem BP P px
        have hCodePX : F.rowDensity (rvValues (indexedLeft px.val)) (indexedRight px.val) c := by
          change F.rowDensity (rvValues (indexedLeft (Fin.append t.val x.val)))
            (indexedRight (Fin.append t.val x.val)) c
          simpa only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right] using hCode
        have hValue : (Ψ u).val = (ω px).val := hcValue.symm.trans
          ((F.rowGammaValue_graph _ (hF _ hpx.1) ⟨indexedRight px.val,hpx.2⟩ c).mp hCodePX)
        have hCast : gammaGroundFormValue Ψ u = gammaGroundFormValue ω px := congrArg (cast (gammaCarrier hc)) hValue
        exact hCast.trans (gammaNativeCoprodForm_left U V ω η px v hImage).symm
      · let px := (Section5.nativeRVGroundDomainEquiv (hc := hc) V).symm
          (Q.domainEquiv.symm ((indexedSigmaEquiv T A).symm ⟨t,x⟩))
        have hu : u.val = Fin.append t.val (@rvRightTag M N hN b a x.val) :=
          hw.symm.trans (congrArg Subtype.val he)
        have hImageRaw := hMapNative.trans
          ((congrArg (fun q => (indexedCoprodEquiv T D A q).val) he).trans (indexedCoprodEquiv_right T D A t x))
        have hImage : v.val = rvRightTag (p+a) px.val := hImageRaw.trans
          (@Section5.rvRightTag_normalized M sM hM (p+a) (p+b) (Fin.append t.val x.val))
        have hCode : G.rowDensity (rvValues t.val) x.val c := by
          apply (F.coprod_rowDensity_right G (rvValues t.val) (fun j => (t.val j).property) x.val c).mp
          have hd := hDensity
          change (F.coprodFormula G).rowDensity _ _ c at hd
          rw [hu] at hd
          simpa only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right] using hd
        have hpx := G.indexed_mem BP Q px
        have hCodePX : G.rowDensity (rvValues (indexedLeft px.val)) (indexedRight px.val) c := by
          change G.rowDensity (rvValues (indexedLeft (Fin.append t.val x.val)))
            (indexedRight (Fin.append t.val x.val)) c
          simpa only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right] using hCode
        have hValue : (Ψ u).val = (η px).val := hcValue.symm.trans
          ((G.rowGammaValue_graph _ (hG _ hpx.1) ⟨indexedRight px.val,hpx.2⟩ c).mp hCodePX)
        have hCast : gammaGroundFormValue Ψ u = gammaGroundFormValue η px := congrArg (cast (gammaCarrier hc)) hValue
        exact hCast.trans (gammaNativeCoprodForm_right U V ω η px v hImage).symm
    unfold gammaNativeCombinedWeight
    rw [hForm,hVolume]
  exact ⟨(gammaNativeCoprodNormalizationHom U V ω η).comp
    (gammaNativeMeasuredNormalizationHom Ψ δ E hWeight)⟩

theorem GammaMeasuredRVSchema.indexedCoprod_class
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .rv)) (L : ℕ)
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
    (hK : ∀ t ∈ T, ((F.coprodFormula G).withBound L).valid (rvValues t))
    (P : F.object.IndexedPresentation BP) (Q : G.object.IndexedPresentation BP)
    (S : ((F.coprodFormula G).withBound L).object.IndexedPresentation BP) :
    gammaGroundMeasuredRVClass (((F.coprodFormula G).withBound L).indexedObject BP hK S) =
      gammaGroundMeasuredRVClass (F.indexedObject BP hF P) + gammaGroundMeasuredRVClass (G.indexedObject BP hG Q) := by
  obtain ⟨e⟩ := F.indexedCoprodChart G L BP hF hG hK P Q S
  exact (gammaGroundMeasuredRVClass_iso (asIso e)).trans (gammaGroundMeasuredRVClass_coprod _ _)

end DiamondIntegral.Section3
