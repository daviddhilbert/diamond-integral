import «section 5».NativeRVSetIsoClasses
import «section 5».RESLiteralFamilyCriterion
import «section 5».NativeUnderlyingBijections
import «section 5».NativeProductBijections

/-! Forgetting the finite label degree gives an actual positive additive
monoid of underlying domains. Finite families have literal tagged domains;
equality in this monoid is an actual same-base definable bijection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5.RESFiniteWitness
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}

theorem nativeRVSetIsoClass_scissor {A C D E : GammaGroundRVObject hc B k}
    (h : gammaGroundRVScissor A C D E) :
    nativeRVSetIsoClass A.domain + nativeRVSetIsoClass C.domain =
      nativeRVSetIsoClass D.domain + nativeRVSetIsoClass E.domain := by
  obtain ⟨U,X,hX,rfl,rfl,rfl,rfl⟩ := h
  change nativeRVSetIsoClass X + nativeRVSetIsoClass (D.domain.sdiff X) =
    nativeRVSetIsoClass D.domain + nativeRVSetIsoClass (GammaGroundDefSet.empty hc B (rawRVSpace 0))
  rw [nativeRVSetIsoClass_empty,add_zero,← nativeRVSetIsoClass_tagged]
  exact (nativeRVSetIsoClass_eq_iff _ _).mpr
    ⟨gammaGroundRVBijectionOfMapIso (gammaGroundRVMapPartitionIso ⟨D⟩ X hX)⟩

def nativeRVPositiveUnderlying : GammaGroundRVKPlus hc B k →+ NativeRVSetIsoClasses hc B :=
  PositiveAdditiveGrothendieck.lift (gammaGroundRVPresentation hc B k) {
    toFun U := nativeRVSetIsoClass U.domain
    iso := fun ⟨e⟩ => (nativeRVSetIsoClass_eq_iff _ _).mpr ⟨e.hom⟩
    empty := nativeRVSetIsoClass_empty
    scissor := nativeRVSetIsoClass_scissor }

theorem nativeRVPositiveUnderlying_class (U : GammaGroundRVObject hc B k) :
    nativeRVPositiveUnderlying (gammaGroundRVClass U) = nativeRVSetIsoClass U.domain :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

def nativeRESPositiveUnderlying : GammaGroundRESKPlus hc B k →+ NativeRVSetIsoClasses hc B :=
  nativeRVPositiveUnderlying.comp gammaGroundRESToRVKPlus

theorem nativeRESPositiveUnderlying_class (U : GammaGroundRESObject hc B k) :
    nativeRESPositiveUnderlying (gammaGroundRESClass U) = nativeRVSetIsoClass U.obj.domain := by
  change nativeRVPositiveUnderlying (gammaGroundRESToRVKPlus (gammaGroundRESClass U)) = _
  rw [gammaGroundRESToRVKPlus_class,nativeRVPositiveUnderlying_class]

def nativeRESGradedUnderlying : GammaGroundRESDirectSum hc B →+ NativeRVSetIsoClasses hc B :=
  DirectSum.toAddMonoid (fun _ => nativeRESPositiveUnderlying)

theorem nativeRESGradedUnderlying_class (U : GammaGroundRESObject hc B k) :
    nativeRESGradedUnderlying (gammaGroundRESDirectSumClass U) = nativeRVSetIsoClass U.obj.domain := by
  change DirectSum.toAddMonoid _ (DirectSum.of _ k (gammaGroundRESClass U)) = _
  rw [DirectSum.toAddMonoid_of,nativeRESPositiveUnderlying_class]

variable (hc B)
def familyRVSet : List (GradedObject hc B) → GammaRVSet hc B
  | [] => ⟨0,GammaGroundDefSet.empty hc B (rawRVSpace 0)⟩
  | U :: L => ⟨1+(U.2.obj.arity+(familyRVSet L).1),
      gammaGroundRVTaggedUnion U.2.obj.domain (familyRVSet L).2⟩

theorem familyRVSet_finite (L : List (GradedObject hc B)) :
    GammaRVFiniteValues hc B (familyRVSet hc B L).2 := by
  induction L with
  | nil => exact Set.finite_empty.image _
  | cons U L ih => exact gammaGroundRVTaggedUnion_finite_values hc B _ _ U.2.property ih

def familyUnderlyingClass (L : List (GradedObject hc B)) : NativeRVSetIsoClasses hc B :=
  nativeRVSetIsoClass (familyRVSet hc B L).2

theorem familyUnderlyingClass_eq (L : List (GradedObject hc B)) :
    familyUnderlyingClass hc B L = nativeRESGradedUnderlying (positiveFamilyClass hc B L) := by
  induction L with
  | nil => exact nativeRVSetIsoClass_empty.trans (map_zero _).symm
  | cons U L ih =>
    change nativeRVSetIsoClass (gammaGroundRVTaggedUnion U.2.obj.domain (familyRVSet hc B L).2) = _
    rw [nativeRVSetIsoClass_tagged,positiveFamilyClass_cons,map_add,nativeRESGradedUnderlying_class]
    exact congrArg (fun x => nativeRVSetIsoClass U.2.obj.domain + x) ih

theorem familyUnderlyingClass_append (L R : List (GradedObject hc B)) :
    familyUnderlyingClass hc B (L ++ R) = familyUnderlyingClass hc B L + familyUnderlyingClass hc B R := by
  rw [familyUnderlyingClass_eq,positiveFamilyClass_append,map_add,←familyUnderlyingClass_eq,←familyUnderlyingClass_eq]

theorem familyUnderlyingClass_singleton (U : GradedObject hc B) :
    familyUnderlyingClass hc B [U] = nativeRVSetIsoClass U.2.obj.domain := by
  rw [familyUnderlyingClass_eq,positiveFamilyClass_singleton,nativeRESGradedUnderlying_class]

theorem familyUnderlyingClass_eq_iff (L R : List (GradedObject hc B)) :
    familyUnderlyingClass hc B L = familyUnderlyingClass hc B R ↔
      Nonempty (GammaGroundBijection (familyRVSet hc B L).2 (familyRVSet hc B R).2) :=
  nativeRVSetIsoClass_eq_iff _ _

end DiamondIntegral.Section5.RESFiniteWitness
