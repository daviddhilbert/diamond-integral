import «section 3».GammaNativeUnitElementaryLift
import «section 3».GammaMeasuredCofullRestriction
import «section 3».GammaMeasuredClassLift
import «section 3».GammaGroundMeasuredRVGenerators
import «section 5».Completed18RVSpecialRelation
import «section 5».NativeZeroStrataPullbacks

/-! The positive native lift and the literal nonzero cone have the same
cofull unit-density VF object. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

theorem gammaBasicPositive_nonzero_labels (t : Fin 1 → CanonicalRV.RVSort M) :
    (t ∈ (@DefSet.carrier LRV M N _ Set.univ (@positiveRV M N Set.univ)) ∧ (t 0).val ≠ iRVZero) ↔
      t ∈ (rvPositiveDomain hc B.real).carrier := by
  change (t ∈ (@DefSet.carrier LRV M N _ Set.univ (@positiveRV M N Set.univ)) ∧ (t 0).val ≠ iRVZero) ↔
    t ∈ (GammaGroundRVObject.ofReal (hc := hc) (ground := B) (rvPositiveObject hc B.real)).domain.carrier
  rw [← Section5.completed18Positive_domain (hc := hc) (B := B),Section5.nativeRVGroundDomain_carrier,
    gammaPositiveNonzeroAt_domain (B := B) (S := Set.univ)]
  have hz : @iRVZero M N = @iRVZero M sM := CanonicalStructure.sortZero_normalize .rv
  rw [hz]

theorem gammaBasicPositive_nonzero_carrier :
    (Section5.nativeVFZeroStratum
      (gammaNativeUnitLift (hc := hc) (gammaPositiveAt (B := B) (S := Set.univ) (Set.subset_univ _)).toGamma).domain Finset.univ).carrier =
      (gammaGroundMeasuredObjectLift (gammaGroundMeasuredRVPositive hc B)).domain.carrier := by
  let V := gammaNativeUnitLift (hc := hc) (gammaPositiveAt (B := B) (S := Set.univ) (Set.subset_univ _)).toGamma
  ext q
  rw [Section5.nativeVFZeroStratum_mem]
  change (q ∈ V.domain.carrier ∧ Section5.nativeVFZeroPattern Finset.univ q) ↔ _
  constructor
  · rintro ⟨⟨u,hu,hv⟩,hn⟩
    have hx : q.1 0 ≠ 0 := (hn 0).mp (Finset.mem_univ _)
    have hkey : (show Fin 1 → CanonicalRV.RVSort M from u.val) = Section2.tupleRV M q.1 := hv.trans (Section5.completed18_tupleRV q.1)
    have hnz : ((show Fin 1 → CanonicalRV.RVSort M from u.val) 0).val ≠ iRVZero := by
      intro hz
      have hz' : rvValues (Section2.tupleRV M q.1) 0 = iRVZero :=
        (congrArg (fun t : Fin 1 → CanonicalRV.RVSort M => (t 0).val) hkey).symm.trans hz
      exact hx ((Section5.rvValues_tupleRV_zero_iff q.1 0).mp hz')
    refine ⟨⟨u.val,(gammaBasicPositive_nonzero_labels (hc := hc) (B := B) u.val).mp ⟨u.property,hnz⟩⟩,hu,hkey⟩
  · rintro ⟨u,hu,hv⟩
    have hpos := (gammaBasicPositive_nonzero_labels (hc := hc) (B := B) u.val).mpr u.property
    have hvN := hv.trans (Section5.completed18_tupleRV q.1).symm
    refine ⟨⟨⟨u.val,hpos.1⟩,hu,hvN⟩,?_⟩
    intro i
    have hi : i=0 := Fin.fin_one_eq_zero i
    subst i
    exact ⟨fun _ hz => hpos.2 ((congrArg (fun t : Fin 1 → CanonicalRV.RVSort M => (t 0).val) hv).trans
      ((Section5.rvValues_tupleRV_zero_iff q.1 0).mpr hz)),fun _ => Finset.mem_univ _⟩

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaBasicPositive_cone_class
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    gammaGroundMeasuredVFClass hκ hs hr hv
      (gammaNativeUnitLift (hc := hc) (gammaPositiveAt (B := B) (S := Set.univ) (Set.subset_univ _)).toGamma) =
    gammaGroundMeasuredVFClass hκ hs hr hv
      (gammaGroundMeasuredObjectLift (gammaGroundMeasuredRVPositive hc B)) := by
  let V := gammaNativeUnitLift (hc := hc) (gammaPositiveAt (B := B) (S := Set.univ) (Set.subset_univ _)).toGamma
  let E := Section5.nativeVFZeroStratum V.domain Finset.univ
  have hE := Section5.nativeVFZeroStratum_subset V.domain Finset.univ
  have hsmall : Section2.vfDimension (V.domain.sdiff E).carrier < ((1 : ℕ) : WithBot ℕ) := by
    apply gammaGround_small_complement_of_generic V.domain E hκ hs hr hv (by decide)
    intro p
    apply (Section5.nativeVFZeroStratum_mem V.domain Finset.univ p.val.val).mpr
    exact ⟨p.val.property,fun i => ⟨fun _ => p.property.ne_zero i,fun _ => Finset.mem_univ _⟩⟩
  have h := gammaMeasuredCofullRestrictionHom hκ hs hr hv V E hE hsmall
  have e := gammaMeasuredHomOfCarrierEq hκ hs hr hv
    (U := V.restrict E hE) (V := gammaGroundMeasuredObjectLift (gammaGroundMeasuredRVPositive hc B)) rfl
    (heq_of_eq (gammaDefSet_eq_of_carrierEq gammaBasicPositive_nonzero_carrier))
    (fun _ _ _ => rfl)
  exact (gammaGroundMeasuredVFClass_iso hκ hs hr hv h).trans (gammaGroundMeasuredVFClass_iso hκ hs hr hv e)

end DiamondIntegral.Section3
