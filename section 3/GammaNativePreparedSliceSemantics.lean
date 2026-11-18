import «section 3».GammaNativePreparedSliceRows
import «section 3».GammaNativeVFSliceDensities
import «section 3».GammaPreparedIndexAttachments

/-! Prepared native volume slices retain global row validity and the
complete transported Gamma density. Their structural and density rows
are interpreted over the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
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
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {p k l : ℕ}
variable (U : GammaObjectAt B Set.univ (p+(k+1)))
variable (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) (N : ℕ)
variable {X : DefSet (M := M) S p 0} {Z : DefSet (M := M) S p l}
variable (T : SpecialBijection X Z) (hT : GammaChainDefinable B T.chain)
variable (hAgreement : ∀ c : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement
  (gammaNativeMeasuredVFSliceSchema U ω N).toRVTemplate
  (rawVFParameter (T.inverseMap c).val) (rawPreparedKey c.val))

include hAgreement in
theorem gammaNativePreparedSlice_valid
    (hValid : ∀ x : Fin p → VF (M := M), (gammaNativeMeasuredVFSliceSchema U ω N).valid (vfValues x)) :
    ∀ t ∈ preparedKeyDomain Z,
      ((gammaNativeMeasuredVFSliceSchema U ω N).recode (GammaParameterRecode.prepared T hT)).valid (rvValues t) := by
  rintro t ⟨c,rfl⟩
  exact (gammaNativeMeasuredVFSliceSchema U ω N).recode_valid (GammaParameterRecode.prepared T hT)
    _ _ (fun j => ((flatKey c.val).2 j).property) (hAgreement c) (hValid (T.inverseMap c).val.1)

variable (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+(k+1)) (rvObjectArity U.object.obj)))
variable (E : GammaGroundBijection A (gammaNativeUnitLift (hc := hc) U.toGamma).domain)
variable (hE : ∀ q, (E.map q).val = q.val)
variable (hP : ∀ q : A,
  ((Section5.nativeMixedCoordinateMap _ (Fin.castAdd (k+1)) (Fin.elim0 : Fin 0 → Fin (rvObjectArity U.object.obj))) q).val ∈
    (Section5.nativeGammaPointDomain (hc := hc) (carrier X) (GammaChainDefinable.source B T.chain hT)).carrier)

include hE hAgreement in
theorem gammaNativePreparedSlice_density
    (q : (Section5.nativeVFPrepareBaseMap A (Section5.nativeSpecialBaseBijection T hT) hP).image)
    (cΓ : (volumeGammaSpace hc).domain)
    (hcValue : (volumeGammaSpace hc).decode cΓ =
      ((((gammaNativeMeasuredLift U ω).form.comp E.map).comp
        (Section5.nativeVFPrepareBaseBijection A (Section5.nativeSpecialBaseBijection T hT) hP).symm.map) q).val) :
    ((gammaNativeMeasuredVFSliceSchema U ω N).recode (GammaParameterRecode.prepared T hT)).rowDensity
      (rvValues (indexedLeft (gammaPreparedIndexAttachment _ q).val.2))
      (indexedRight (gammaPreparedIndexAttachment _ q).val.2) cΓ := by
  let TΓ := Section5.nativeSpecialBaseBijection (hc := hc) T hT
  let W := Section5.nativeVFPrepareBaseBijection A TΓ hP
  let a := W.symm.map q
  let u := E.map a
  let c : Z := ⟨(q.val.1 ∘ Fin.castAdd (k+1),q.val.2 ∘ Fin.castAdd (rvObjectArity U.object.obj)),
    gammaPartialBase_base_mem A TΓ hP q⟩
  have hInv := gammaPartialBase_inverse_basepoint A TΓ hP q
  change (TΓ.symm.map ⟨c.val,c.property⟩).val.1 = a.val.1 ∘ Fin.castAdd (k+1) at hInv
  rw [Section5.nativeSpecialBaseBijection_inverse] at hInv
  have hBase : (T.inverseMap c).val.1 = u.val.1 ∘ Fin.castAdd (k+1) :=
    hInv.trans (congrArg (fun z => z.1 ∘ Fin.castAdd (k+1)) (hE a)).symm
  have hOld : u.val.2 = q.val.2 ∘ Fin.natAdd l :=
    (congrArg Prod.snd (hE a)).trans (gammaPartialBase_inverse_labels A TΓ hP q)
  have hSource := gammaNativeMeasuredVFSliceSchema_point_density U ω N u cΓ hcValue
  have hSource' : (gammaNativeMeasuredVFSliceSchema U ω N).rowDensity
      (rawVFParameter (T.inverseMap c).val) (q.val.2 ∘ Fin.natAdd l) cΓ := by
    change (gammaNativeMeasuredVFSliceSchema U ω N).rowDensity
      (vfValues (T.inverseMap c).val.1) (q.val.2 ∘ Fin.natAdd l) cΓ
    rw [hBase,← hOld]
    exact hSource
  have hRows := (GammaVolumeParameterRecode.prepared T hT).volumeObject_rows
    (gammaNativeMeasuredVFSliceSchema U ω N).toRVTemplate _ _ (hAgreement c)
  have hTarget := (hRows.density (q.val.2 ∘ Fin.natAdd l) (gammaVolumeCodeRV cΓ)).mp hSource'
  rw [gammaPreparedIndexAttachment_value]
  simp only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right]
  exact hTarget

end DiamondIntegral.Section3
