import «section 3».GammaMeasuredIndexedWeights
import «section 3».GammaNativeMeasuredRestrictions
import «section 3».GammaNativeMeasuredIsomorphisms
import IntegrationSection6.GammaSchemaIndexedRestrictionIso

/-! Index restriction preserves literal volume tuples and the entire
Gamma density, using the existing identity chart over the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a d k : ℕ}
variable {T E : Set (Fin p → RV (M := M))}
variable {R S : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem GammaMeasuredRVSchema.indexedRestrictionChart
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (BQ : GammaFiniteGraphPresentation B p d E S)
    (hBase : ∀ t ∈ E, BQ.totalVolume t = BP.totalVolume t)
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hQ : ∀ t ∈ E, F.valid (rvValues t))
    (P : F.object.IndexedPresentation BP) (Q : F.object.IndexedPresentation BQ)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (p+a)) Set.univ)
    (hSub : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ A ⊆
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain (gammaUniversalObject P.toGamma).object.obj))
    (hA : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ A =
      indexedDomain E (fun t => F.object.rowDomain (rvValues t)))
    (hΓ : GammaSetDefinable B {w : Point (M := M) 0 (p+a) |
      w.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ A}) :
    Nonempty (GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (gammaRestrictAt (gammaUniversalObject P.toGamma) A hSub hΓ)
        ((F.indexedForm BP hF P).comp (gammaNativeRestrictedLabelInclusion (gammaUniversalObject P.toGamma) A hSub hΓ)))
      (F.indexedObject BQ hQ Q)) := by
  let U := gammaUniversalObject P.toGamma
  let V := gammaUniversalObject Q.toGamma
  let Z := gammaRestrictAt U A hSub hΓ
  let e := F.object.indexedRestrictionIso BP BQ hBase P Q A hSub hA hΓ
  let ω := (F.indexedForm BP hF P).comp (gammaNativeRestrictedLabelInclusion U A hSub hΓ)
  let η := F.indexedForm BQ hQ Q
  refine ⟨gammaNativeMeasuredNormalizationHom ω η e (fun u => ?_)⟩
  let v := (Section5.nativeRVGroundIso e).map u
  let b := gammaNativeRestrictedLabelInclusion U A hSub hΓ u
  have hLabels : v.val = b.val := rfl
  have hRaw : (Section5.nativeRVGroundVolume Z u).val = (Section5.nativeRVGroundVolume U b).val := by
    rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
    rfl
  have hv := F.indexed_mem BQ Q v
  have hVolume : (Section5.nativeRVGroundVolume Z u).val = (Section5.nativeRVGroundVolume V v).val := by
    rw [hRaw,F.indexed_volume BP P b,F.indexed_volume BQ Q v,hLabels]
    have hBase' : BQ.totalVolume (indexedLeft b.val) = BP.totalVolume (indexedLeft b.val) := by
      simpa only [hLabels] using hBase (indexedLeft v.val) hv.1
    exact congrArg (fun q => Fin.append q (F.object.rowValue (rvValues (indexedLeft b.val)) (indexedRight b.val))) hBase'.symm
  have hDensity : gammaGroundFormValue ω u = gammaGroundFormValue η v := by
    rfl
  unfold gammaNativeCombinedWeight
  rw [hVolume,hDensity]

end DiamondIntegral.Section3
