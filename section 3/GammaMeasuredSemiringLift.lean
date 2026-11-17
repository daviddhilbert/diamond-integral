import «section 3».GammaMeasuredClosureClassLift
import «section 3».GammaMeasuredLiftProducts
import «section 3».GammaGroundMeasuredRVSemiring
import «section 3».GammaGroundMeasuredVFSemiring
import «section 5».Completed18LocalLiftSurjective

/-! The actual surjective Gamma-valued semiring lift at the manuscript's
original base. This construction does not assume the kernel comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaMeasuredUnitLiftHom : GammaGroundZeroMeasuredVFHom
    (gammaGroundMeasuredObjectLift (GammaGroundMeasuredRVObject.unit hc B))
    (GammaGroundMeasuredVFData.unit hc B) where
  bijection := GammaGroundBijection.ofCarrierEq (by
    apply Set.eq_univ_iff_forall.mpr
    intro q
    refine ⟨⟨Fin.elim0,Set.mem_univ _⟩,?_,?_⟩
    · change (Fin.elim0 : Fin 0 → CanonicalRV.RVSort M) = q.2
      exact Subsingleton.elim _ _
    · funext i
      exact i.elim0)
  preserves _ := rfl

variable (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem gammaMeasuredLift_semiring_empty (k : ℕ) :
    gammaGroundMeasuredVFSemiringClass C hc hv
      (gammaGroundMeasuredObjectLift (GammaGroundMeasuredRVObject.empty hc C.base k)) = 0 :=
  (gammaGroundMeasuredVFSemiringClass_iso C hc hv
    (gammaMeasuredLiftEmptyHom C.uncountable.le C.saturated C.small_real hv)).trans
      (gammaGroundMeasuredVFSemiringClass_empty C hc hv)

theorem gammaMeasuredLift_semiring_scissor {k : ℕ}
    {A B D E : GammaGroundMeasuredRVObject hc C.base k} (h : gammaGroundMeasuredRVScissor A B D E) :
    gammaGroundMeasuredVFSemiringClass C hc hv (gammaGroundMeasuredObjectLift A) +
      gammaGroundMeasuredVFSemiringClass C hc hv (gammaGroundMeasuredObjectLift B) =
      gammaGroundMeasuredVFSemiringClass C hc hv (gammaGroundMeasuredObjectLift D) +
        gammaGroundMeasuredVFSemiringClass C hc hv (gammaGroundMeasuredObjectLift E) := by
  obtain ⟨U,X,hX,hA,hB,hD,hE⟩ := h
  subst A
  subst B
  subst D
  subst E
  have hs := congrArg (gammaGroundMeasuredVFKPlusToSemiring C hc hv)
    (gammaMeasuredLift_class_scissor C.uncountable.le C.saturated C.small_real hv U X hX)
  simpa only [map_add,gammaGroundMeasuredVFKPlusToSemiring_class,
    gammaMeasuredLift_semiring_empty,add_zero] using hs

def gammaMeasuredRVSemiringLiftInvariant :
    PositiveGrothendieck.Invariant (gammaGroundMeasuredRVSemiringPresentation hc C.base)
      (R := GammaGroundMeasuredVFPositiveSemiring C hc hv) where
  toFun A := gammaGroundMeasuredVFSemiringClass C hc hv (gammaGroundMeasuredObjectLift A.2)
  iso := by
    rintro A B ⟨k,U,V,⟨e⟩,rfl,rfl⟩
    exact gammaGroundMeasuredVFSemiringClass_iso C hc hv
      (gammaMeasuredClosureArrowLift C.uncountable C.saturated C.model00 C.small_real C.small_gamma
        (C.fieldBase.gamma_closure_generated C.base.gamma) hv e.hom)
  empty := gammaMeasuredLift_semiring_empty C hc hv 0
  unit := (gammaGroundMeasuredVFSemiringClass_iso C hc hv (k := 0) gammaMeasuredUnitLiftHom).trans
    (gammaGroundMeasuredVFSemiringClass_unit C hc hv)
  product A B := (gammaGroundMeasuredVFSemiringClass_iso C hc hv
    (gammaMeasuredLiftProductHom C.uncountable.le C.saturated C.small_real hv A.2 B.2)).trans
      (gammaGroundMeasuredVFSemiringClass_product C hc hv _ _)
  scissor := by
    rintro A B D E (⟨k,U,V,W,X,h,rfl,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl,rfl⟩)
    · exact gammaMeasuredLift_semiring_scissor C hc hv h
    · simp only [gammaMeasuredLift_semiring_empty,add_zero]

def gammaContextMeasuredSemiringLift : GammaGroundMeasuredRVPositiveSemiring hc C.base →+*
    GammaGroundMeasuredVFPositiveSemiring C hc hv :=
  PositiveGrothendieck.lift (gammaGroundMeasuredRVSemiringPresentation hc C.base)
    (gammaMeasuredRVSemiringLiftInvariant C hc hv)

@[simp] theorem gammaContextMeasuredSemiringLift_class {k : ℕ} (U : GammaGroundMeasuredRVObject hc C.base k) :
    gammaContextMeasuredSemiringLift C hc hv (gammaGroundMeasuredRVSemiringClass U) =
      gammaGroundMeasuredVFSemiringClass C hc hv (gammaGroundMeasuredObjectLift U) :=
  PositiveGrothendieck.lift_of (gammaGroundMeasuredRVSemiringPresentation hc C.base)
    (gammaMeasuredRVSemiringLiftInvariant C hc hv) ⟨k,U⟩

theorem gammaContextMeasuredSemiringLift_surjective :
    Function.Surjective (gammaContextMeasuredSemiringLift C hc hv) := by
  apply Section5.positivePresentationHom_surjective_of_classes (gammaGroundMeasuredVFSemiringPresentation C hc hv)
  rintro ⟨k,U⟩
  obtain ⟨W,hW⟩ := gammaMeasuredVFObject_class_preimage C.uncountable C.saturated C.model00 C.small_real hv U
  have he := congrArg (gammaGroundMeasuredVFKPlusToSemiring C hc hv) hW
  simp only [gammaGroundMeasuredVFKPlusToSemiring_class] at he
  exact ⟨gammaGroundMeasuredRVSemiringClass W,(gammaContextMeasuredSemiringLift_class C hc hv W).trans he.symm⟩

end DiamondIntegral.Section3
