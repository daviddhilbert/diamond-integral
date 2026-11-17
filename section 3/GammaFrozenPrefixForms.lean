import «section 3».GammaFrozenPrefixMaps

/-! The complete Gamma form on an actual unary slice lift is the
original measured VF form at the included point. This is an equality of
actual values for every point, with all old RV labels retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ}
variable (U : GammaObjectAt B Set.univ (p+1))
variable (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) (N : ℕ)
variable (x : Fin p → VF (M := M)) (hF : (gammaNativeMeasuredVFSliceSchema U ω N).valid (vfValues x))
variable (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (rvObjectArity U.object.obj) 1
  ((gammaNativeMeasuredVFSliceSchema U ω N).object.rowDomain (vfValues x))
  ((gammaNativeMeasuredVFSliceSchema U ω N).object.rowVolume (vfValues x)))

def gammaNativeSliceRowOriginalPoint
    (q : (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain) :
    (gammaNativeUnitLift (hc := hc) U.toGamma).domain :=
  ⟨(gammaNativeSliceRowInclusion U ω N x hF P q).val,(gammaNativeSliceRowInclusion U ω N x hF P q).property⟩

theorem gammaNativeSliceRow_form_value
    (q : (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain) :
    ((gammaNativeMeasuredLift (gammaUniversalObject P.toGamma)
      ((gammaNativeMeasuredVFSliceSchema U ω N).rawRowForm (vfValues x) hF P)).form q).val =
        ((gammaNativeMeasuredLift U ω).form (gammaNativeSliceRowOriginalPoint U ω N x hF P q)).val := by
  let F := gammaNativeMeasuredVFSliceSchema U ω N
  let u := gammaNativeLiftLabel (gammaUniversalObject P.toGamma) q
  let θ := F.rawRowForm (vfValues x) hF P
  obtain ⟨c,hcValue⟩ := (volumeGammaSpace hc).onto (θ u).val
  have hCode : F.rowDensity (vfValues x) q.val.2 c :=
    (F.rawRow_density (vfValues x) hF P q.val.2 c).mpr ⟨u,rfl,hcValue.symm⟩
  have hRows := gammaMeasuredLabelSchema_density ((gammaNativeVFSliceSchema U).withBound N) ω
    (vfValues x) (fun j => (x j).property) q.val.2 c
  obtain ⟨_,v,hv,hω⟩ := hRows.mp hCode
  have hLabel : v = gammaNativeLiftLabel U (gammaNativeSliceRowOriginalPoint U ω N x hF P q) := Subtype.ext hv
  exact hcValue.symm.trans (hω.symm.trans (congrArg (fun z => (ω z).val) hLabel))

theorem gammaNativeSliceRow_weight
    (q : (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain) :
    gammaGroundMeasuredVFWeight (gammaNativeMeasuredLift (gammaUniversalObject P.toGamma)
      ((gammaNativeMeasuredVFSliceSchema U ω N).rawRowForm (vfValues x) hF P)) q =
        gammaGroundMeasuredVFWeight (gammaNativeMeasuredLift U ω) (gammaNativeSliceRowOriginalPoint U ω N x hF P q) :=
  congrArg (fun z => (cast (gammaCarrier hc) z).val) (gammaNativeSliceRow_form_value U ω N x hF P q)


theorem gammaNativeSliceRowOriginalPoint_injective :
    Function.Injective (gammaNativeSliceRowOriginalPoint U ω N x hF P) := by
  intro q r h
  apply gammaNativeSliceRowInclusion_injective U ω N x hF P
  exact Subtype.ext (congrArg Subtype.val h)

end DiamondIntegral.Section3
