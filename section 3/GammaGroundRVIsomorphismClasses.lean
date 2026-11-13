import «section 3».GammaGroundRVPartitions
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.Algebra.Group.TypeTags.Basic

/-! Positive equality means an actual same-Gamma-ground definable
bijection. No cancellation or geometric integration input is used. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

instance gammaGroundRVMapMonoidal : MonoidalCategory (GammaGroundRVMapObject hc ground k) := monoidalOfHasFiniteCoproducts _
instance gammaGroundRVMapSymmetric : SymmetricCategory (GammaGroundRVMapObject hc ground k) := symmetricOfHasFiniteCoproducts _

abbrev GammaGroundRVIsoClasses (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) := Additive (Skeleton (GammaGroundRVMapObject hc ground k))

def gammaGroundRVIsoClass (U : GammaGroundRVObject hc ground k) : GammaGroundRVIsoClasses hc ground k :=
  Additive.ofMul (toSkeleton (⟨U⟩ : GammaGroundRVMapObject hc ground k))

theorem gammaGroundRVIsoClass_eq_iff {U V : GammaGroundRVObject hc ground k} :
    gammaGroundRVIsoClass U = gammaGroundRVIsoClass V ↔ Nonempty (U ≅ V) := by
  change toSkeleton (⟨U⟩ : GammaGroundRVMapObject hc ground k) = toSkeleton (⟨V⟩ : GammaGroundRVMapObject hc ground k) ↔ _
  rw [toSkeleton_eq_toSkeleton_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨asIso (show U ⟶ V from gammaGroundRVBijectionOfMapIso e)⟩
  · rintro ⟨e⟩
    exact ⟨gammaGroundRVMapIsoOfBijection e.hom⟩

@[simp] theorem gammaGroundRVIsoClass_empty :
    gammaGroundRVIsoClass (GammaGroundRVObject.empty hc ground k) = 0 := by
  change toSkeleton (GammaGroundRVMapObject.empty hc ground k) = (1 : Skeleton (GammaGroundRVMapObject hc ground k))
  rw [Skeleton.one_eq]
  exact congr_toSkeleton_of_iso (gammaGroundRVMapEmptyIsInitial.uniqueUpToIso initialIsInitial)

theorem gammaGroundRVIsoClass_coprod (U V : GammaGroundRVObject hc ground k) :
    gammaGroundRVIsoClass (U.coprod V) = gammaGroundRVIsoClass U + gammaGroundRVIsoClass V := by
  let A : GammaGroundRVMapObject hc ground k := ⟨U⟩
  let B : GammaGroundRVMapObject hc ground k := ⟨V⟩
  change toSkeleton (A.coprod B) = toSkeleton A * toSkeleton B
  calc
    _ = toSkeleton (A ⨿ B) := congr_toSkeleton_of_iso
      (colimit.isoColimitCocone
        { cocone := BinaryCofan.mk (gammaGroundRVMapInl A B) (gammaGroundRVMapInr A B)
          isColimit := gammaGroundRVMapCoprodIsColimit A B }).symm
    _ = _ := Skeleton.toSkeleton_tensorObj A B

theorem gammaGroundRVIsoClass_scissor {A B D E : GammaGroundRVObject hc ground k}
    (h : gammaGroundRVScissor A B D E) :
    gammaGroundRVIsoClass A + gammaGroundRVIsoClass B = gammaGroundRVIsoClass D + gammaGroundRVIsoClass E := by
  obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
  subst A
  subst B
  subst D
  subst E
  rw [gammaGroundRVIsoClass_empty, add_zero, ← gammaGroundRVIsoClass_coprod]
  apply gammaGroundRVIsoClass_eq_iff.mpr
  exact ⟨asIso (show _ ⟶ U from gammaGroundRVBijectionOfMapIso
    (gammaGroundRVMapPartitionIso (⟨U⟩ : GammaGroundRVMapObject hc ground k) X hX))⟩

def gammaGroundRVKPlusToIsoClasses : GammaGroundRVKPlus hc ground k →+ GammaGroundRVIsoClasses hc ground k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundRVPresentation hc ground k) {
    toFun := gammaGroundRVIsoClass
    iso := gammaGroundRVIsoClass_eq_iff.mpr
    empty := gammaGroundRVIsoClass_empty
    scissor := gammaGroundRVIsoClass_scissor }

@[simp] theorem gammaGroundRVKPlusToIsoClasses_class (U : GammaGroundRVObject hc ground k) :
    gammaGroundRVKPlusToIsoClasses (gammaGroundRVClass U) = gammaGroundRVIsoClass U :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem gammaGroundRVClass_eq_iff_iso {U V : GammaGroundRVObject hc ground k} :
    gammaGroundRVClass U = gammaGroundRVClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    apply gammaGroundRVIsoClass_eq_iff.mp
    simpa only [gammaGroundRVKPlusToIsoClasses_class] using congrArg gammaGroundRVKPlusToIsoClasses h
  · rintro ⟨e⟩
    exact gammaGroundRVClass_iso e

end DiamondIntegral.Section3
