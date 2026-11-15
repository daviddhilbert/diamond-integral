import «section 5».Completed18RVGradedComparison
import «section 5».Completed18VFComparison
import «section 3».GammaGroundCitedUnmeasuredIntegral
import IntegrationSection6.GammaNonzeroGlobalLift

/-! The completed [18] lift is a semiring map on the exact local
positive presentations and sends every object to its actual full-label lift. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section3 DiamondIntegral.Section4
namespace DiamondIntegral.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

theorem completed18_tupleRV (x : Fin k → Section2.VF M) :
    @SpecialTransformations.Section4.tupleRV M N hN k x=Section2.tupleRV M x := by
  funext i
  apply Subtype.ext
  exact rvCode_eq (x i).val (x i).property

theorem groundRVAt_volume_eq (U : GammaGroundRVObject hc B k)
    (u : rvObjectDomain (groundRVAt U).object.obj) :
    (rvObjectVolume (groundRVAt U).object.obj u).val=
      (U.volume ((groundRVAtDomainEquiv U).symm u)).val := by
  obtain ⟨a,ha,hv⟩ := groundRVAt_volume U u
  have he : a=(groundRVAtDomainEquiv U).symm u := Subtype.ext ha
  exact hv.symm.trans (congrArg (fun a : U.domain => (U.volume a).val) he)

theorem groundRVAt_lift_domain (U : GammaGroundRVObject hc B k) :
    (groundRVAt U).toGamma.lift=(gammaGroundObjectLift U).carrier := by
  ext q
  change (∃ u : rvObjectDomain (groundRVAt U).object.obj,u.val=q.2 ∧
    (rvObjectVolume (groundRVAt U).object.obj u).val=@SpecialTransformations.Section4.tupleRV M N hN k q.1) ↔ _
  rw [completed18_tupleRV]
  constructor
  · rintro ⟨u,hu,hv⟩
    exact ⟨(groundRVAtDomainEquiv U).symm u,hu,(groundRVAt_volume_eq U u).symm.trans hv⟩
  · rintro ⟨u,hu,hv⟩
    refine ⟨groundRVAtDomainEquiv U u,hu,?_⟩
    exact (groundRVAt_volume_eq U _).trans (by simpa only [Equiv.symm_apply_apply] using hv)

theorem nativeVFPositiveGround_lift_class (U : GammaGroundRVObject hc B k) :
    nativeVFPositiveGround (gammaAllLiftClass (groundRVAt U).toGamma)=
      gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U) := by
  unfold gammaAllLiftClass
  rw [nativeVFPositiveGround_class]
  apply nativePositiveVFClass_bijection
  apply GammaGroundBijection.ofCarrierEq
  exact groundRVAt_lift_domain U

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
  (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)

def completed18LocalLift : GammaGroundRVPositiveSemiring hc B →+* GammaGroundVFPositiveSemiring hc B :=
  nativeVFPositiveGround.comp ((gammaNonzeroGlobalLiftAt (S := Set.univ) hκ hs h00 hr hB).comp
    completed18RVPositiveEquiv.toRingHom)

theorem completed18LocalLift_class (U : GammaGroundRVObject hc B k) :
    completed18LocalLift hκ hs h00 hr hB (gammaGroundRVSemiringClass U)=
      gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U) := by
  change nativeVFPositiveGround (gammaNonzeroGlobalLiftAt hκ hs h00 hr hB
    (completed18RVPositiveEquiv (gammaGroundRVSemiringClass U)))=_
  rw [completed18RVPositiveEquiv_class]
  change nativeVFPositiveGround (gammaNonzeroGlobalLiftAt hκ hs h00 hr hB
    (gammaNonzeroGradedClassAt (groundRVAt U) (groundRVAt_full U)))=_
  rw [gammaNonzeroGlobalLiftAt_class]
  exact nativeVFPositiveGround_lift_class U

end DiamondIntegral.Section5
