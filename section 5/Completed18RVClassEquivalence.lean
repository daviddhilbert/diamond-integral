import «section 5».Completed18RVIsomorphisms
import «section 3».GammaGroundRVGradedComparison

/-! The completed [18] full-weight classes and the local positive
fixed-degree RV scissors classify precisely the same actual bijections. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section3 DiamondIntegral.Section4
namespace DiamondIntegral.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

def groundRVClassNative (a : GammaGroundRVKPlus hc B k) :
    GammaNonzeroClassesAt (B := B) (S := Set.univ) k :=
  gammaNonzeroClassAt (groundRVAt (gammaGroundRVRepresentative a))
    (groundRVAt_full (gammaGroundRVRepresentative a))

theorem groundRVClassNative_class (U : GammaGroundRVObject hc B k) :
    groundRVClassNative (gammaGroundRVClass U) = gammaNonzeroClassAt (groundRVAt U) (groundRVAt_full U) := by
  apply Subtype.ext
  obtain ⟨e⟩ := gammaGroundRVClass_eq_iff_iso.mp (gammaGroundRVRepresentative_class (gammaGroundRVClass U))
  exact gammaIsoClassAt_iso (groundRVAtIso e.hom)

def nativeRVClassRepresentative (a : GammaNonzeroClassesAt (B := B) (S := Set.univ) k) :
    GammaObjectAt B Set.univ k := a.property.choose

theorem nativeRVClassRepresentative_class (a : GammaNonzeroClassesAt (B := B) (S := Set.univ) k) :
    gammaIsoClassAt (nativeRVClassRepresentative a) = a.val := a.property.choose_spec.1

theorem nativeRVClassRepresentative_full (a : GammaNonzeroClassesAt (B := B) (S := Set.univ) k) :
    GammaFullWeightAt (nativeRVClassRepresentative a) := a.property.choose_spec.2

def nativeRVClassGround (a : GammaNonzeroClassesAt (B := B) (S := Set.univ) k) :
    GammaGroundRVKPlus hc B k := gammaGroundRVClass
      (nativeRVGroundObject (nativeRVClassRepresentative a) (nativeRVClassRepresentative_full a))

theorem nativeRVClassGround_class (U : GammaObjectAt B Set.univ k) (hU : GammaFullWeightAt U) :
    nativeRVClassGround (hc := hc) (gammaNonzeroClassAt U hU) =
      gammaGroundRVClass (nativeRVGroundObject U hU) := by
  obtain ⟨e⟩ := gammaIsoClassAt_eq_iff.mp (nativeRVClassRepresentative_class (gammaNonzeroClassAt U hU))
  exact gammaGroundRVClass_iso (asIso (show _ ⟶ _ from nativeRVGroundIso e))

theorem nativeRVClassGround_ground (a : GammaGroundRVKPlus hc B k) :
    nativeRVClassGround (groundRVClassNative a) = a := by
  obtain ⟨U,rfl⟩ := gammaGroundRVClass_surjective a
  rw [groundRVClassNative_class,nativeRVClassGround_class]
  exact gammaGroundRVClass_iso (asIso (show _ ⟶ _ from groundRVObjectRoundTrip U))

theorem groundRVClassNative_native (a : GammaNonzeroClassesAt (B := B) (S := Set.univ) k) :
    groundRVClassNative (nativeRVClassGround (hc := hc) a) = a := by
  change groundRVClassNative (gammaGroundRVClass _) = a
  rw [groundRVClassNative_class]
  apply Subtype.ext
  exact (gammaIsoClassAt_iso (nativeRVObjectRoundTrip _ (nativeRVClassRepresentative_full a))).trans
    (nativeRVClassRepresentative_class a)

def completed18RVClassEquiv : GammaGroundRVKPlus hc B k ≃
    GammaNonzeroClassesAt (B := B) (S := Set.univ) k where
  toFun := groundRVClassNative
  invFun := nativeRVClassGround
  left_inv := nativeRVClassGround_ground
  right_inv := groundRVClassNative_native

end DiamondIntegral.Section5
