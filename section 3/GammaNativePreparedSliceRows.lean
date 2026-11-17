import «section 3».GammaNativeVFSliceLiftDomains
import «section 3».GammaPartialBaseNormalForm
import «section 3».GammaMeasuredRowAgreements
import «section 5».NativeSpecialBaseBridge
import Integration7.GammaPreparedVolumeRows

/-! Preparing the VF prefix of a native full lift gives precisely the
recoded volume-slice rows. The original base and actual inverse special
transformation determine every row. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
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

theorem gammaNativePreparedSlice_rows
    (U : GammaObjectAt B Set.univ (p+(k+1)))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) (N : ℕ)
    {X : DefSet (M := M) S p 0} {Z : DefSet (M := M) S p l}
    (T : SpecialBijection X Z) (hT : GammaChainDefinable B T.chain)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+(k+1)) (rvObjectArity U.object.obj)))
    (hLift : A.carrier = (gammaNativeUnitLift (hc := hc) U.toGamma).domain.carrier)
    (hP : ∀ q : A,
      ((Section5.nativeMixedCoordinateMap _ (Fin.castAdd (k+1)) (Fin.elim0 : Fin 0 → Fin (rvObjectArity U.object.obj))) q).val ∈
        (Section5.nativeGammaPointDomain (hc := hc) (carrier X) (GammaChainDefinable.source B T.chain hT)).carrier)
    (hAgreement : ∀ c : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement
      (gammaNativeMeasuredVFSliceSchema U ω N).toRVTemplate
      (rawVFParameter (T.inverseMap c).val) (rawPreparedKey c.val))
    (c : Z) (y : Fin (k+1) → Section2.VF M) (r : Fin (rvObjectArity U.object.obj) → RV (M := M)) :
    (Fin.append c.val.1 y,Fin.append c.val.2 r) ∈
        (Section5.nativeVFPrepareBaseMap A
          (Section5.nativeSpecialBaseBijection T hT) hP).image.carrier ↔
      ((gammaNativeMeasuredVFSliceSchema U ω N).recode (GammaParameterRecode.prepared T hT)).object.rowVolume
        (rawPreparedKey c.val) r (@Section2.tupleRV M sM hM (k+1) y) := by
  let cN : Section5.nativeGammaPointDomain (hc := hc) (carrier Z) (GammaChainDefinable.target B T.chain hT) :=
    ⟨c.val,c.property⟩
  have hNormal := gammaPartialBase_normalForm A
    (Section5.nativeSpecialBaseBijection T hT) hP cN y r
  rw [Section5.nativeSpecialBaseBijection_inverse,hLift] at hNormal
  have hRows := (GammaVolumeParameterRecode.prepared T hT).volumeObject_rows
    (gammaNativeMeasuredVFSliceSchema U ω N).toRVTemplate _ _ (hAgreement c)
  exact hNormal.trans ((gammaNativeVFSliceSchema_lift U (T.inverseMap c).val.1 y r).trans
    (hRows.1.2 (rvValues r) (rvValues (@Section2.tupleRV M sM hM (k+1) y))))

end DiamondIntegral.Section3
