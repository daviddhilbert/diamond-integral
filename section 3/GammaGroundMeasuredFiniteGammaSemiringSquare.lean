import «section 3».GammaGroundMeasuredFiniteGammaSemiring
import «section 3».GammaGroundMeasuredGammaSemiringLift
import «section 3».GammaGroundMeasuredRESGradedSemiring
import «section 3».GammaGroundMeasuredGammaRVMorphisms
/-! The actual measured coefficient square, including multiplication. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundMeasuredFiniteGammaToGammaInvariant : PositiveGrothendieck.Invariant
    (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground) (R := GammaGroundMeasuredGammaPositiveSemiring hc ground) where
  toFun A := gammaGroundMeasuredGammaSemiringClass A.2.obj
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact gammaGroundMeasuredGammaSemiringClass_iso ((gammaGroundMeasuredFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).ι.mapIso e)
  empty := gammaGroundMeasuredGammaSemiringClass_empty
  unit := gammaGroundMeasuredGammaSemiringClass_unit
  product A B := gammaGroundMeasuredGammaSemiringClass_product A.2.obj B.2.obj
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      exact gammaGroundMeasuredGammaSemiringClass_scissor hs
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      simp only [GammaGroundMeasuredFiniteGammaObject.empty, gammaGroundMeasuredGammaSemiringClass_empty, add_zero]

def gammaGroundMeasuredFiniteGammaToGammaSemiring : GammaGroundMeasuredFiniteGammaPositiveSemiring hc ground →+* GammaGroundMeasuredGammaPositiveSemiring hc ground :=
  PositiveGrothendieck.lift (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground) gammaGroundMeasuredFiniteGammaToGammaInvariant

@[simp] theorem gammaGroundMeasuredFiniteGammaToGammaSemiring_class (A : GammaGroundMeasuredFiniteGammaObject hc ground k) :
    gammaGroundMeasuredFiniteGammaToGammaSemiring (gammaGroundMeasuredFiniteGammaSemiringClass A) = gammaGroundMeasuredGammaSemiringClass A.obj :=
  PositiveGrothendieck.lift_of (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground) gammaGroundMeasuredFiniteGammaToGammaInvariant ⟨k, A⟩

def gammaGroundMeasuredFiniteGammaToRESInvariant : PositiveGrothendieck.Invariant
    (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground) (R := GammaGroundMeasuredRESDirectSum (M := M) hc ground) where
  toFun A := gammaGroundMeasuredRESDirectSumClass A.2.resLift
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    obtain ⟨E⟩ := gammaGroundMeasuredFiniteGammaHom_lift_iso e.hom
    exact congrArg (DirectSum.of (GammaGroundMeasuredRESKPlus hc ground) k) (gammaGroundMeasuredRESClass_iso E)
  empty := by
    apply gammaGroundMeasuredRESDirectSumToRV_injective
    change DirectSum.map (fun _ => gammaGroundMeasuredRESToRVKPlus)
      (DirectSum.of (GammaGroundMeasuredRESKPlus hc ground) 0 (gammaGroundMeasuredRESClass _)) = gammaGroundMeasuredRESDirectSumToRV 0
    rw [DirectSum.map_of, gammaGroundMeasuredRESToRVKPlus_class, map_zero]
    change DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) 0 (gammaGroundMeasuredRVClass (GammaGroundMeasuredGammaObject.empty hc ground 0).rvLift) = 0
    rw [gammaGroundMeasuredGammaRVClass_empty, map_zero]
  unit := by
    apply gammaGroundMeasuredRESDirectSumToRV_injective
    change DirectSum.map (fun _ => gammaGroundMeasuredRESToRVKPlus)
      (DirectSum.of (GammaGroundMeasuredRESKPlus hc ground) 0 (gammaGroundMeasuredRESClass _)) = gammaGroundMeasuredRESDirectSumToRV 1
    rw [DirectSum.map_of, gammaGroundMeasuredRESToRVKPlus_class, gammaGroundMeasuredRESDirectSumToRV_one]
    change DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) 0 (gammaGroundMeasuredRVClass (GammaGroundMeasuredGammaObject.unit hc ground).rvLift) = _
    rw [gammaGroundMeasuredGammaRVClass_unit]
    rfl
  product A B := by
    apply gammaGroundMeasuredRESDirectSumToRV_injective
    rw [gammaGroundMeasuredRESDirectSumToRV_mul]
    change DirectSum.map (fun _ => gammaGroundMeasuredRESToRVKPlus)
      (DirectSum.of (GammaGroundMeasuredRESKPlus hc ground) (A.1 + B.1) (gammaGroundMeasuredRESClass _)) =
      DirectSum.map (fun _ => gammaGroundMeasuredRESToRVKPlus) (DirectSum.of (GammaGroundMeasuredRESKPlus hc ground) A.1 (gammaGroundMeasuredRESClass _)) *
      DirectSum.map (fun _ => gammaGroundMeasuredRESToRVKPlus) (DirectSum.of (GammaGroundMeasuredRESKPlus hc ground) B.1 (gammaGroundMeasuredRESClass _))
    rw [DirectSum.map_of, DirectSum.map_of, DirectSum.map_of,
      gammaGroundMeasuredRESToRVKPlus_class, gammaGroundMeasuredRESToRVKPlus_class, gammaGroundMeasuredRESToRVKPlus_class, DirectSum.of_mul_of]
    apply congrArg (DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) (A.1 + B.1))
    exact (gammaGroundMeasuredGammaRVClass_product A.2.obj B.2.obj).trans (gammaGroundMeasuredRVClassMul_class _ _).symm
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      have hh : gammaGroundMeasuredGammaClass a.obj + gammaGroundMeasuredGammaClass b.obj = gammaGroundMeasuredGammaClass d.obj + gammaGroundMeasuredGammaClass e.obj :=
        positiveClass_scissor (gammaGroundMeasuredGammaPresentation hc ground k) hs
      apply gammaGroundMeasuredRESDirectSumToRV_injective
      simp only [map_add, gammaGroundMeasuredRESDirectSumClass, gammaGroundMeasuredRESDirectSumToRV, DirectSum.map_of, gammaGroundMeasuredRESToRVKPlus_class]
      rw [← map_add, ← map_add]
      apply congrArg (DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k)
      have ht := congrArg gammaGroundMeasuredGammaToRVKPlus hh
      have ht' : gammaGroundMeasuredRVClass a.obj.rvLift + gammaGroundMeasuredRVClass b.obj.rvLift = gammaGroundMeasuredRVClass d.obj.rvLift + gammaGroundMeasuredRVClass e.obj.rvLift := by
        simpa only [map_add, gammaGroundMeasuredGammaToRVKPlus_class] using ht
      exact ht'
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      apply gammaGroundMeasuredRESDirectSumToRV_injective
      simp only [map_add, gammaGroundMeasuredRESDirectSumClass, gammaGroundMeasuredRESDirectSumToRV, DirectSum.map_of, gammaGroundMeasuredRESToRVKPlus_class]
      change DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k (gammaGroundMeasuredRVClass (GammaGroundMeasuredGammaObject.empty hc ground k).rvLift) +
        DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) 0 (gammaGroundMeasuredRVClass (GammaGroundMeasuredGammaObject.empty hc ground 0).rvLift) = _
      change DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k (gammaGroundMeasuredRVClass (GammaGroundMeasuredGammaObject.empty hc ground k).rvLift) +
        DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) 0 (gammaGroundMeasuredRVClass (GammaGroundMeasuredGammaObject.empty hc ground 0).rvLift) =
        DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) 0 (gammaGroundMeasuredRVClass (GammaGroundMeasuredGammaObject.empty hc ground 0).rvLift) +
        DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) 0 (gammaGroundMeasuredRVClass (GammaGroundMeasuredGammaObject.empty hc ground 0).rvLift)
      simp only [gammaGroundMeasuredGammaRVClass_empty, map_zero, add_zero]

def gammaGroundMeasuredFiniteGammaToRESSemiring : GammaGroundMeasuredFiniteGammaPositiveSemiring hc ground →+* GammaGroundMeasuredRESDirectSum (M := M) hc ground :=
  PositiveGrothendieck.lift (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground) gammaGroundMeasuredFiniteGammaToRESInvariant

@[simp] theorem gammaGroundMeasuredFiniteGammaToRESSemiring_class (A : GammaGroundMeasuredFiniteGammaObject hc ground k) :
    gammaGroundMeasuredFiniteGammaToRESSemiring (gammaGroundMeasuredFiniteGammaSemiringClass A) = gammaGroundMeasuredRESDirectSumClass A.resLift :=
  PositiveGrothendieck.lift_of (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground) gammaGroundMeasuredFiniteGammaToRESInvariant ⟨k, A⟩

def gammaGroundMeasuredRESToRVSemiring : GammaGroundMeasuredRESDirectSum (M := M) hc ground →+* GammaGroundMeasuredRVPositiveSemiring hc ground :=
  gammaGroundMeasuredRVDirectSumToPresentation.comp gammaGroundMeasuredRESGradedInclusion

@[simp] theorem gammaGroundMeasuredRESToRVSemiring_class (A : GammaGroundMeasuredRESObject (M := M) hc ground k) :
    gammaGroundMeasuredRESToRVSemiring (gammaGroundMeasuredRESDirectSumClass A) = gammaGroundMeasuredRVSemiringClass A.obj := by
  change gammaGroundMeasuredRVDirectSumToPresentation (DirectSum.map (fun _ => gammaGroundMeasuredRESToRVKPlus)
    (DirectSum.of (GammaGroundMeasuredRESKPlus hc ground) k (gammaGroundMeasuredRESClass A))) = _
  rw [DirectSum.map_of, gammaGroundMeasuredRESToRVKPlus_class]
  exact gammaGroundMeasuredRVDirectSumToPresentation_class A.obj

theorem gammaGroundMeasuredRESToRVSemiring_injective : Function.Injective (gammaGroundMeasuredRESToRVSemiring (M := M) (hc := hc) (ground := ground)) :=
  (gammaGroundMeasuredRVSemiringEquivDirectSum (M := M) (hc := hc) (ground := ground)).symm.injective.comp gammaGroundMeasuredRESGradedInclusion_injective

theorem gammaGroundMeasuredFiniteGamma_semiring_square :
    (gammaGroundMeasuredRESToRVSemiring (M := M) (hc := hc) (ground := ground)).comp (gammaGroundMeasuredFiniteGammaToRESSemiring (hc := hc)) =
      gammaGroundMeasuredGammaToRVSemiring.comp gammaGroundMeasuredFiniteGammaToGammaSemiring := by
  apply PositiveGrothendieck.hom_ext (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground)
  rintro ⟨k, A⟩
  change gammaGroundMeasuredRESToRVSemiring (gammaGroundMeasuredFiniteGammaToRESSemiring (gammaGroundMeasuredFiniteGammaSemiringClass A)) =
    gammaGroundMeasuredGammaToRVSemiring (gammaGroundMeasuredFiniteGammaToGammaSemiring (gammaGroundMeasuredFiniteGammaSemiringClass A))
  rw [gammaGroundMeasuredFiniteGammaToRESSemiring_class, gammaGroundMeasuredRESToRVSemiring_class,
    gammaGroundMeasuredFiniteGammaToGammaSemiring_class, gammaGroundMeasuredGammaToRVSemiring_class]
  rfl

end DiamondIntegral.Section3
