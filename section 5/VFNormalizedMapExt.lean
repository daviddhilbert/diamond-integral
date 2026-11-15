import «section 5».NativeLiftGroundTransfer
import «section 3».CompletionTensor

/-! The Section 3 lifting surjection determines every normalized map on
the actual VF Grothendieck ring from its values on genuine RV lifts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {R : Type} [CommRing R]

theorem vfNormalizedMap_ext (I : OriginalBaseUnmeasuredLiftInput hc B)
    (f g : GammaGroundVFGrothendieckRing hc B →+* R)
    (h : ∀ {k : ℕ} (U : GammaGroundRVObject hc B k),
      f (of (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U))) =
        g (of (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U)))) : f = g := by
  have he : (f.comp ofRingHom).comp I.lift = (g.comp ofRingHom).comp I.lift := by
    apply positivePresentationHom_ext (gammaGroundRVSemiringPresentation hc B)
    intro A
    change f (of (I.lift (gammaGroundRVSemiringClass A.2))) =
      g (of (I.lift (gammaGroundRVSemiringClass A.2)))
    rw [I.lift_class]
    exact h A.2
  apply ringHom_ext
  intro a
  obtain ⟨u,rfl⟩ := I.surjective a
  exact RingHom.congr_fun he u

variable {C : Base (M := M)}
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B sn D → DefinableOverBase C sn D)

def sortedTransferVFRing : GammaGroundVFGrothendieckRing hc B →+* GammaGroundVFGrothendieckRing hc C :=
  ringCompletionMap (sortedTransferVFPositive H)

theorem sortedTransferVFRing_class (A : GammaGroundFiniteVFObject hc B) :
    sortedTransferVFRing H (of (gammaGroundVFSemiringClass A)) =
      of (gammaGroundVFSemiringClass (sortedTransferFiniteVFObject H A)) := by
  rw [sortedTransferVFRing,ringCompletionMap_of,sortedTransferVFPositive_class]

theorem sortedTransferVFRing_lift {k : ℕ} (U : GammaGroundRVObject hc B k) :
    sortedTransferVFRing H (of (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U))) =
      of (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite (sortedTransferRVObject H U))) := by
  rw [sortedTransferVFRing,ringCompletionMap_of,sortedTransferVFPositive_lift]

end DiamondIntegral.Section5
