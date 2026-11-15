import «section 5».RESUngradedPositiveFamilies
import «section 5».NativeRESClasses

/-! The literal tagged finite family has the sum of its actual ungraded
RES classes, independently of all chosen label degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5.RESFiniteWitness
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
open Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k l : ℕ}

theorem nativeUngradedClass_tagged (U : GammaGroundRESObject hc B k)
    (V : GammaGroundRESObject hc B l) :
    nativeUngradedClass hc (nativeRESObjectOfGammaSet hc B
      (gammaGroundRVTaggedUnion U.obj.domain V.obj.domain)
      (gammaGroundRVTaggedUnion_finite_values hc B _ _ U.property V.property)) =
      nativeUngradedClass hc U + nativeUngradedClass hc V := by
  let D := gammaGroundRVTaggedUnion U.obj.domain V.obj.domain
  let T := nativeRESObjectOfGammaSet hc B D
    (gammaGroundRVTaggedUnion_finite_values hc B _ _ U.property V.property)
  let X := (gammaGroundRVLeftTag U.obj.domain V.obj.arity).image
  let Y := (gammaGroundRVRightTag V.obj.domain U.obj.arity).image
  have hX : X.carrier ⊆ T.obj.domain.carrier := fun _ h => Or.inl h
  have hd : (T.obj.domain.sdiff X).carrier = Y.carrier := by
    ext t
    constructor
    · rintro ⟨ht,hn⟩
      exact ht.resolve_left hn
    · intro ht
      exact ⟨Or.inr ht,fun hx => Set.disjoint_left.mp
        (gammaGroundRVTaggedImages_disjoint U.obj.domain V.obj.domain) hx ht⟩
  have hL : nativeUngradedClass hc (T.restrict X hX) = nativeUngradedClass hc U :=
    nativeUngradedClass_bijection hc _ _ (gammaGroundRVLeftTagBijection U.obj.domain V.obj.arity).symm
  have hR : nativeUngradedClass hc (T.restrict (T.obj.domain.sdiff X) (fun _ h => h.1)) =
      nativeUngradedClass hc V :=
    nativeUngradedClass_bijection hc _ _ ((gammaGroundRVRightTagBijection V.obj.domain U.obj.arity).symm.comp
      (gammaGroundBijectionOfCarrierEq _ _ hd))
  exact (nativeUngradedClass_cut hc T X hX).symm.trans (congrArg₂ (· + ·) hL hR)

variable (hc B)
def familyNativeObject (L : List (GradedObject hc B)) :
    GammaGroundRESObject hc B (familyRVSet hc B L).1 :=
  nativeRESObjectOfGammaSet hc B (familyRVSet hc B L).2 (familyRVSet_finite hc B L)

def familyUngradedClass (L : List (GradedObject hc B)) : RESDimensionFreeRing.Ring B :=
  nativeUngradedClass hc (familyNativeObject hc B L)

theorem familyUngradedClass_eq (L : List (GradedObject hc B)) :
    familyUngradedClass hc B L = nativeUngradedHom hc B (of (positiveFamilyClass hc B L)) := by
  induction L with
  | nil =>
    have he := nativeUngradedClass_bijection hc (familyNativeObject hc B [])
      (GammaGroundRESObject.empty hc B 0) (GammaGroundBijection.id _)
    exact he.trans ((nativeUngradedClass_empty hc B 0).trans (by simp [positiveFamilyClass]))
  | cons U L ih =>
    have he := nativeUngradedClass_tagged U.2 (familyNativeObject hc B L)
    change familyUngradedClass hc B (U :: L) = _ at he
    rw [positiveFamilyClass_cons,map_add,map_add]
    change _ = nativeUngradedHom hc B (Section3RESClassCuts.ordinaryClass U.2) + _
    rw [nativeUngradedHom_class,←ih]
    exact he

def reducedPositiveHom : GammaGroundRESDirectSum hc B →+* RESDimensionFreeReduction.Ring B :=
  ((RESDimensionFreeReduction.fromOrdinary B).comp
    (Section3RESRingEquivalences.ordinary hc B).symm.toRingHom).comp ofRingHom

theorem reducedPositiveHom_positiveClass {k : ℕ} (a : RVMeasuredCharts.RESChart B k) :
    reducedPositiveHom hc B (positiveClass hc B a) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) := by
  change RESDimensionFreeReduction.fromOrdinary B
    ((Section3RESRingEquivalences.ordinary hc B).symm (of (positiveClass hc B a))) = _
  rw [of_positiveClass,RingEquiv.symm_apply_apply]

theorem familyReducedClass_eq (L : List (GradedObject hc B)) :
    RESDimensionFreeReduction.quotient B (familyUngradedClass hc B L) =
      reducedPositiveHom hc B (positiveFamilyClass hc B L) := by
  rw [familyUngradedClass_eq]
  rfl

theorem positiveRelation_reduced_eq {L R : GammaGroundRESDirectSum hc B}
    (h : PositiveRelationSum (relationPairs hc B) L R) :
    reducedPositiveHom hc B L = reducedPositiveHom hc B R := by
  let x := (Section3RESRingEquivalences.ordinary hc B).symm (of L - of R)
  have hx : x ∈ RESDimensionFreeRing.degreeIdeal B ⊔ RESOrdinaryReduction.fibreIdeal B := by
    apply (relationIdeal_mem_iff hc B x).mp
    simpa only [x,RingEquiv.apply_symm_apply] using h.difference_mem
  have hz : RESDimensionFreeReduction.fromOrdinary B x = 0 := by
    rw [←RESDimensionFreeReduction.kernel_fromOrdinary] at hx
    exact hx
  change RESDimensionFreeReduction.fromOrdinary B ((Section3RESRingEquivalences.ordinary hc B).symm (of L)) =
    RESDimensionFreeReduction.fromOrdinary B ((Section3RESRingEquivalences.ordinary hc B).symm (of R))
  exact sub_eq_zero.mp (by simpa only [x,map_sub] using hz)

end DiamondIntegral.Section5.RESFiniteWitness
