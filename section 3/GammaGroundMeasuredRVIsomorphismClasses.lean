import «section 3».GammaGroundMeasuredRVPartitions
import «section 3».GammaGroundMeasuredRVRepresentatives
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

instance gammaGroundMeasuredRVMapMonoidal : MonoidalCategory (GammaGroundMeasuredRVMapObject hc ground k) := monoidalOfHasFiniteCoproducts _
instance gammaGroundMeasuredRVMapSymmetric : SymmetricCategory (GammaGroundMeasuredRVMapObject hc ground k) := symmetricOfHasFiniteCoproducts _

abbrev GammaGroundMeasuredRVIsoClasses (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) := Additive (Skeleton (GammaGroundMeasuredRVMapObject hc ground k))

def gammaGroundMeasuredRVIsoClass (U : GammaGroundMeasuredRVObject hc ground k) : GammaGroundMeasuredRVIsoClasses hc ground k :=
  Additive.ofMul (toSkeleton (⟨U⟩ : GammaGroundMeasuredRVMapObject hc ground k))

theorem gammaGroundMeasuredRVIsoClass_eq_iff {U V : GammaGroundMeasuredRVObject hc ground k} :
    gammaGroundMeasuredRVIsoClass U = gammaGroundMeasuredRVIsoClass V ↔ Nonempty (U ≅ V) := by
  change toSkeleton (⟨U⟩ : GammaGroundMeasuredRVMapObject hc ground k) = toSkeleton (⟨V⟩ : GammaGroundMeasuredRVMapObject hc ground k) ↔ _
  rw [toSkeleton_eq_toSkeleton_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨asIso (show U ⟶ V from gammaGroundMeasuredRVHomOfMapIso e)⟩
  · rintro ⟨e⟩
    exact ⟨gammaGroundMeasuredRVMapIsoOfHom e.hom⟩

@[simp] theorem gammaGroundMeasuredRVIsoClass_empty :
    gammaGroundMeasuredRVIsoClass (GammaGroundMeasuredRVObject.empty hc ground k) = 0 := by
  change toSkeleton (GammaGroundMeasuredRVMapObject.empty hc ground k) = (1 : Skeleton (GammaGroundMeasuredRVMapObject hc ground k))
  rw [Skeleton.one_eq]
  exact congr_toSkeleton_of_iso (gammaGroundMeasuredRVMapEmptyIsInitial.uniqueUpToIso initialIsInitial)

theorem gammaGroundMeasuredRVIsoClass_coprod (U V : GammaGroundMeasuredRVObject hc ground k) :
    gammaGroundMeasuredRVIsoClass (U.coprod V) = gammaGroundMeasuredRVIsoClass U + gammaGroundMeasuredRVIsoClass V := by
  let A : GammaGroundMeasuredRVMapObject hc ground k := ⟨U⟩
  let B : GammaGroundMeasuredRVMapObject hc ground k := ⟨V⟩
  change toSkeleton (A.coprod B) = toSkeleton A * toSkeleton B
  calc
    _ = toSkeleton (A ⨿ B) := congr_toSkeleton_of_iso
      (colimit.isoColimitCocone
        { cocone := BinaryCofan.mk (gammaGroundMeasuredRVMapInl A B) (gammaGroundMeasuredRVMapInr A B)
          isColimit := gammaGroundMeasuredRVMapCoprodIsColimit A B }).symm
    _ = _ := Skeleton.toSkeleton_tensorObj A B

theorem gammaGroundMeasuredRVIsoClass_scissor {A B D E : GammaGroundMeasuredRVObject hc ground k}
    (h : gammaGroundMeasuredRVScissor A B D E) :
    gammaGroundMeasuredRVIsoClass A + gammaGroundMeasuredRVIsoClass B = gammaGroundMeasuredRVIsoClass D + gammaGroundMeasuredRVIsoClass E := by
  obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
  subst A
  subst B
  subst D
  subst E
  rw [gammaGroundMeasuredRVIsoClass_empty, add_zero, ← gammaGroundMeasuredRVIsoClass_coprod]
  apply gammaGroundMeasuredRVIsoClass_eq_iff.mpr
  exact ⟨asIso (show _ ⟶ U from gammaGroundMeasuredRVPartitionHom U X hX)⟩

def gammaGroundMeasuredRVKPlusToIsoClasses : GammaGroundMeasuredRVKPlus hc ground k →+ GammaGroundMeasuredRVIsoClasses hc ground k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundMeasuredRVPresentation hc ground k) {
    toFun := gammaGroundMeasuredRVIsoClass
    iso := gammaGroundMeasuredRVIsoClass_eq_iff.mpr
    empty := gammaGroundMeasuredRVIsoClass_empty
    scissor := gammaGroundMeasuredRVIsoClass_scissor }

@[simp] theorem gammaGroundMeasuredRVKPlusToIsoClasses_class (U : GammaGroundMeasuredRVObject hc ground k) :
    gammaGroundMeasuredRVKPlusToIsoClasses (gammaGroundMeasuredRVClass U) = gammaGroundMeasuredRVIsoClass U :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem gammaGroundMeasuredRVClass_eq_iff_iso {U V : GammaGroundMeasuredRVObject hc ground k} :
    gammaGroundMeasuredRVClass U = gammaGroundMeasuredRVClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    apply gammaGroundMeasuredRVIsoClass_eq_iff.mp
    simpa only [gammaGroundMeasuredRVKPlusToIsoClasses_class] using congrArg gammaGroundMeasuredRVKPlusToIsoClasses h
  · rintro ⟨e⟩
    exact gammaGroundMeasuredRVClass_iso e

end DiamondIntegral.Section3
