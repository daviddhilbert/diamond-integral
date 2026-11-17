import «section 3».GammaNativePartialBaseIndexedComparison
import «section 3».GammaNativePreparedSliceSemantics
import «section 3».GammaPartialBaseFullMeasured
import «section 3».GammaNativeTypedMeasuredBridge

/-! The actual prepared indexed volume slices represent the original
native measured RV class. The proof uses the real partial-base special
preparation and the checked VF-fixed indexed-lift comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k l : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativePreparedSlice_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (U : GammaObjectAt B Set.univ (p+(k+1)))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) (N : ℕ)
    (hValid : ∀ x : Fin p → VF (M := M), (gammaNativeMeasuredVFSliceSchema U ω N).valid (vfValues x))
    {X : DefSet (M := M) S p 0} {Z : DefSet (M := M) S p l}
    (T : SpecialBijection X Z) (hT : GammaChainDefinable B T.chain) (hZ : IsRVPullback (carrier Z))
    (hInput : ∀ q : typedLift U.object.obj, (q.val.1 ∘ Fin.castAdd (k+1),Fin.elim0) ∈ carrier X)
    (hAgreement : ∀ c : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement
      (gammaNativeMeasuredVFSliceSchema U ω N).toRVTemplate
      (rawVFParameter (T.inverseMap c).val) (rawPreparedKey c.val))
    (BP : PreparedIndexPresentation B Z)
    (P : ((gammaNativeMeasuredVFSliceSchema U ω N).recode (GammaParameterRecode.prepared T hT)).object.IndexedPresentation BP) :
    gammaNativeSpecialClass U ω =
      gammaMeasuredPrincipalValue (((gammaNativeMeasuredVFSliceSchema U ω N).recode (GammaParameterRecode.prepared T hT)).indexedObject
        BP (gammaNativePreparedSlice_valid U ω N T hT hAgreement hValid) P) := by
  let H := typedLift U.object.obj
  let hH := gammaNativeTypedLift_definable U
  let A := (gammaNativeTypedMeasuredData (hc := hc) U ω).domain
  let E := gammaNativeTypedLiftBijection (hc := hc) U
  let TΓ := Section5.nativeSpecialBaseBijection (hc := hc) T hT
  have hP : ∀ q : A,
      ((Section5.nativeMixedCoordinateMap A (Fin.castAdd (k+1)) (Fin.elim0 : Fin 0 → Fin (rvObjectArity U.object.obj))) q).val ∈
        (Section5.nativeGammaPointDomain (hc := hc) (carrier X) (GammaChainDefinable.source B T.chain hT)).carrier := by
    intro q
    change (q.val.1 ∘ Fin.castAdd (k+1),q.val.2 ∘ Fin.elim0) ∈ carrier X
    exact (Prod.ext rfl (Subsingleton.elim _ _) :
      (q.val.1 ∘ Fin.castAdd (k+1),Fin.elim0) = (q.val.1 ∘ Fin.castAdd (k+1),q.val.2 ∘ Fin.elim0)) ▸
        hInput ⟨q.val,q.property⟩
  let W := Section5.nativeVFPrepareBaseBijection A TΓ hP
  let Y := (Section5.nativeVFPrepareBaseMap A TΓ hP).image
  let hfin := Section5.nativeVFPrepareBaseMap_finite hκ hs h00 hr A TΓ hP (gammaNativeTypedMeasuredData U ω).finite
  let η := (gammaNativeTypedMeasuredData U ω).form.comp W.symm.map
  let fP := gammaPartialBaseFullMeasured hκ hs h00 hr T hT H hH hP
    (gammaNativeTypedMeasuredData U ω).finite (gammaNativeTypedMeasuredData U ω).form hv
  let f := ((gammaNativeTypedFullMeasured hκ hs hr hv U ω).symm hκ hs hr hv).comp hκ hs hr hv fP
  have hLift : A.carrier = (gammaNativeUnitLift (hc := hc) U.toGamma).domain.carrier := typedLift_carrier U.object.obj
  have hFollow : ∀ q, (f.map.map q).val.1 ∘ Fin.castAdd (k+1) =
      (T.toMap ⟨((gammaNativeSourcePoint U q).val.1 ∘ Fin.castAdd (k+1),Fin.elim0),hInput (gammaNativeSourcePoint U q)⟩).val.1 := by
    intro q
    let a := E.symm.map q
    let b := (Section5.nativeVFBaseParameterMap A _ hP) a
    have hb : (⟨b.val,b.property⟩ : X) =
        ⟨((gammaNativeSourcePoint U q).val.1 ∘ Fin.castAdd (k+1),Fin.elim0),hInput (gammaNativeSourcePoint U q)⟩ :=
      Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))
    have hTv := Section5.nativeGammaPointBijection_apply
      (GammaChainDefinable.source B T.chain hT) (GammaChainDefinable.target B T.chain hT)
      (Section5.nativeSpecialBaseIso T hT) b
    have hTval := hTv.trans (congrArg (fun u : X => (T.toMap u).val) hb)
    change Fin.append (TΓ.map b).val.1 (a.val.1 ∘ Fin.natAdd p) ∘ Fin.castAdd (k+1) = _
    funext j
    exact (Fin.append_left _ _ j).trans (congrFun (congrArg Prod.fst hTval) j)
  have hOther : ∀ q, ∀ j : Fin (p+(k+1)), j ∉ Set.range (Fin.castAdd (k+1) : Fin p → Fin (p+(k+1))) →
      (f.map.map q).val.1 j = (gammaNativeSourcePoint U q).val.1 j := by
    intro q j
    let a := E.symm.map q
    refine Fin.addCases ?_ ?_ j
    · intro i hi
      exact False.elim (hi ⟨i,rfl⟩)
    · intro i _
      change (Fin.append (TΓ.map ((Section5.nativeVFBaseParameterMap A _ hP) a)).val.1 (a.val.1 ∘ Fin.natAdd p)) (Fin.natAdd p i) = a.val.1 (Fin.natAdd p i)
      exact Fin.append_right _ _ i
  exact gammaNativePartialBase_indexed_family_comparison hκ hs h00 hr hg hv C₀ hBC₀ U ω T hT hZ hInput
    BP _ (gammaNativePreparedSlice_valid U ω N T hT hAgreement hValid) P Y
    (gammaPartialBase_base_mem A TΓ hP)
    (gammaNativePreparedSlice_rows U ω N T hT A hLift hP hAgreement)
    hfin η (gammaNativePreparedSlice_density U ω N T hT hAgreement A E (fun _ => rfl) hP)
    f hFollow hOther

end DiamondIntegral.Section3
