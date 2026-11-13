import «section 3».GammaGroundCitedBoundedIntegral
import «section 3».GammaGroundCitedUnmeasuredIntegral
import «section 3».GammaGroundFiniteVFCoproducts
import «section 3».PresentationAdditiveNormalForm

/-! The actual Gamma-ground dimension filtration embeds in its universal
cartesian presentation, relative to the accepted global and bounded lifts. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {C : GammaGroundContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y}

def gammaGroundVFKPlusToSemiring {k : ℕ} : GammaGroundVFKPlus hc C.base k →+ GammaGroundVFPositiveSemiring hc C.base :=
  gammaGroundFiniteVFKPlusToSemiring.comp gammaGroundVFToFiniteKPlus

@[simp] theorem gammaGroundVFKPlusToSemiring_class {k : ℕ} (U : GammaGroundVFObject hc C.base k) :
    gammaGroundVFKPlusToSemiring (gammaGroundVFClass U) = gammaGroundVFSemiringClass (.ofBound U) := by
  change gammaGroundFiniteVFKPlusToSemiring (gammaGroundVFToFiniteKPlus (gammaGroundVFClass U)) = _
  rw [gammaGroundVFToFiniteKPlus_class, gammaGroundFiniteVFKPlusToSemiring_class]

theorem gammaGroundBoundedLift_global_compat (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (D : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) (k : ℕ) :
    H.lift.toAddMonoidHom.comp (gammaGroundRVBoundedInclude (k := k)) =
      gammaGroundVFKPlusToSemiring.comp (D.lift k) := by
  apply DirectSum.addHom_ext
  intro i x
  have he : (H.lift.toAddMonoidHom.comp (gammaGroundRVKPlusToSemiring (k := i.val))) =
      (gammaGroundVFKPlusToSemiring.comp (D.lift k)).comp
        (DirectSum.of (fun j : Fin (k + 1) => GammaGroundRVKPlus hc C.base j.val) i) := by
    apply positiveAdditivePresentationHom_ext (gammaGroundRVPresentation hc C.base i.val)
    intro U
    change H.lift (gammaGroundRVKPlusToSemiring (gammaGroundRVClass U)) =
      gammaGroundVFKPlusToSemiring (D.lift k (gammaGroundRVBoundedClass i U))
    rw [gammaGroundRVKPlusToSemiring_class, H.lift_class, D.lift_class,
      gammaGroundVFKPlusToSemiring_class]
    rfl
  change H.lift (gammaGroundRVBoundedInclude (DirectSum.of _ i x)) = _
  rw [gammaGroundRVBoundedInclude_of]
  exact DFunLike.congr_fun he x

theorem gammaGroundVFKPlusToSemiring_injective (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (D : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) (k : ℕ) :
    Function.Injective (gammaGroundVFKPlusToSemiring (C := C) (hc := hc) (k := k)) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := D.surjective k a
  obtain ⟨y, rfl⟩ := D.surjective k b
  have he := gammaGroundBoundedLift_global_compat H D k
  have hx := DFunLike.congr_fun he x
  have hy := DFunLike.congr_fun he y
  change H.lift (gammaGroundRVBoundedInclude x) = gammaGroundVFKPlusToSemiring (D.lift k x) at hx
  change H.lift (gammaGroundRVBoundedInclude y) = gammaGroundVFKPlusToSemiring (D.lift k y) at hy
  have hk : gammaGroundRVBoundedSpecialCongruence (ground := C.base) (k := k) hc x y := by
    change (gammaGroundRVSpecialCongruence hc C.base).mk' (gammaGroundRVBoundedInclude x) =
      (gammaGroundRVSpecialCongruence hc C.base).mk' (gammaGroundRVBoundedInclude y)
    apply (RingCon.eq _).mpr
    rw [H.kernel]
    exact hx.trans (hab.trans hy.symm)
  rw [D.kernel k] at hk
  exact hk

theorem gammaGroundVFKPlusToSemiring_raise {k l : ℕ} (hkl : k ≤ l) :
    (gammaGroundVFKPlusToSemiring (C := C) (hc := hc) (k := l)).comp (gammaGroundVFRaiseKPlus hkl) =
      (gammaGroundVFKPlusToSemiring (C := C) (hc := hc) (k := k)) := by
  change gammaGroundFiniteVFKPlusToSemiring.comp (gammaGroundVFToFiniteKPlus.comp (gammaGroundVFRaiseKPlus hkl)) = _
  rw [gammaGroundVFToFiniteKPlus_raise]
  rfl

theorem gammaGroundVFRaiseKPlus_injective (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (D : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) {k l : ℕ} (hkl : k ≤ l) :
    Function.Injective (gammaGroundVFRaiseKPlus (hc := hc) (ground := C.base) hkl) := by
  intro a b hab
  apply gammaGroundVFKPlusToSemiring_injective H D k
  have he := gammaGroundVFKPlusToSemiring_raise (C := C) (hc := hc) hkl
  exact (DFunLike.congr_fun he a).symm.trans
    ((congrArg (gammaGroundVFKPlusToSemiring (C := C) (hc := hc)) hab).trans (DFunLike.congr_fun he b))

theorem gammaGroundFiniteVFKPlusToSemiring_surjective :
    Function.Surjective (gammaGroundFiniteVFKPlusToSemiring (hc := hc) (ground := C.base)) := by
  apply positivePresentation_additive_surjective (gammaGroundVFSemiringPresentation hc C.base)
  intro U
  exact ⟨gammaGroundFiniteVFClass U, gammaGroundFiniteVFKPlusToSemiring_class U⟩

theorem gammaGroundFiniteVFKPlusToSemiring_injective (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (D : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) :
    Function.Injective (gammaGroundFiniteVFKPlusToSemiring (hc := hc) (ground := C.base)) := by
  intro a b hab
  obtain ⟨U, rfl⟩ := gammaGroundFiniteVFClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundFiniteVFClass_surjective b
  let k := max U.vfArity V.vfArity
  let A := U.toBound.raise (le_max_left U.vfArity V.vfArity)
  let B := V.toBound.raise (le_max_right U.vfArity V.vfArity)
  have he : gammaGroundVFClass A = gammaGroundVFClass B := by
    apply gammaGroundVFKPlusToSemiring_injective H D k
    rw [gammaGroundVFKPlusToSemiring_class, gammaGroundVFKPlusToSemiring_class]
    change gammaGroundVFSemiringClass U = gammaGroundVFSemiringClass V
    simpa only [gammaGroundFiniteVFKPlusToSemiring_class] using hab
  have hf := congrArg (gammaGroundVFToFiniteKPlus (hc := hc) (ground := C.base)) he
  rw [gammaGroundVFToFiniteKPlus_class, gammaGroundVFToFiniteKPlus_class] at hf
  exact hf

def gammaGroundFiniteVFSemiringAddEquiv (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (D : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) :
    GammaGroundFiniteVFKPlus hc C.base ≃+ GammaGroundVFPositiveSemiring hc C.base :=
  AddEquiv.ofBijective gammaGroundFiniteVFKPlusToSemiring
    ⟨gammaGroundFiniteVFKPlusToSemiring_injective H D, gammaGroundFiniteVFKPlusToSemiring_surjective⟩

end DiamondIntegral.Section3
