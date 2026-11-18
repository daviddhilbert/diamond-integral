import «section 3».GammaNativeMeasuredVFSlices
import «section 3».GammaNativeLiftMembership

/-! Freezing a VF prefix of a native full lift gives exactly the unary
or higher-dimensional lift of its actual RV volume slice. Zero volume
coordinates are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawMixedSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k : ℕ}

theorem gammaNativeVFSliceSchema_lift (U : GammaObjectAt B Set.univ (p+k))
    (x : Fin p → Section2.VF M) (y : Fin k → Section2.VF M) (r : Fin (rvObjectArity U.object.obj) → RV (M := M)) :
    (Fin.append x y,r) ∈ (gammaNativeUnitLift (hc := hc) U.toGamma).domain.carrier ↔
      (gammaNativeVFSliceSchema U).rowVolume (vfValues x) r (@Section2.tupleRV M sM hM k y) := by
  have he : @Section2.tupleRV M sM hM (p+k) (Fin.append x y) =
      Fin.append (fun j => @rv M sM hM (x j)) (@Section2.tupleRV M sM hM k y) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Section2.tupleRV,Section2.rv,tupleRV,Fin.append_left,Fin.append_right] <;> rfl
  constructor
  · intro hq
    obtain ⟨u,hu,hv⟩ := (gammaNativeLift_membership U (Fin.append x y,r)).mp hq
    apply (gammaNativeVFSliceSchema_volume U x r (@Section2.tupleRV M sM hM k y)).mpr
    exact ⟨Section5.nativeRVGroundDomainEquiv U u,hu,
      (gammaNativeRVGroundVolume_value U u).symm.trans (hv.trans he)⟩
  · intro hrow
    obtain ⟨u,hu,hv⟩ := (gammaNativeVFSliceSchema_volume U x r (@Section2.tupleRV M sM hM k y)).mp hrow
    let v := (Section5.nativeRVGroundDomainEquiv (hc := hc) U).symm u
    apply (gammaNativeLift_membership U (Fin.append x y,r)).mpr
    exact ⟨v,hu,(gammaNativeRVGroundVolume_value U v).trans (hv.trans he.symm)⟩

end DiamondIntegral.Section3
