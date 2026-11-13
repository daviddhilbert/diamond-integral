import «section 3».GammaGroundFiniteGammaSemiring
import «section 3».GammaGroundGammaSemiringLift
import «section 3».GammaGroundRESGradedSemiring
import «section 3».GammaGroundGammaRESLift
/-! The actual unmeasured coefficient square, including multiplication. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundFiniteGammaToGammaInvariant : PositiveGrothendieck.Invariant
    (gammaGroundFiniteGammaSemiringPresentation hc ground) (R := GammaGroundGammaPositiveSemiring hc ground) where
  toFun A := gammaGroundGammaSemiringClass A.2.obj
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact gammaGroundGammaSemiringClass_iso ((gammaGroundFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).ι.mapIso e)
  empty := gammaGroundGammaSemiringClass_empty
  unit := gammaGroundGammaSemiringClass_unit
  product A B := gammaGroundGammaSemiringClass_product A.2.obj B.2.obj
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      exact gammaGroundGammaSemiringClass_scissor hs
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      simp only [GammaGroundFiniteGammaObject.empty, gammaGroundGammaSemiringClass_empty, add_zero]

def gammaGroundFiniteGammaToGammaSemiring : GammaGroundFiniteGammaPositiveSemiring hc ground →+* GammaGroundGammaPositiveSemiring hc ground :=
  PositiveGrothendieck.lift (gammaGroundFiniteGammaSemiringPresentation hc ground) gammaGroundFiniteGammaToGammaInvariant

@[simp] theorem gammaGroundFiniteGammaToGammaSemiring_class (A : GammaGroundFiniteGammaObject hc ground k) :
    gammaGroundFiniteGammaToGammaSemiring (gammaGroundFiniteGammaSemiringClass A) = gammaGroundGammaSemiringClass A.obj :=
  PositiveGrothendieck.lift_of (gammaGroundFiniteGammaSemiringPresentation hc ground) gammaGroundFiniteGammaToGammaInvariant ⟨k, A⟩

def gammaGroundFiniteGammaToRESInvariant : PositiveGrothendieck.Invariant
    (gammaGroundFiniteGammaSemiringPresentation hc ground) (R := GammaGroundRESDirectSum (M := M) hc ground) where
  toFun A := gammaGroundRESDirectSumClass A.2.resLift
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    obtain ⟨E⟩ := gammaGroundFiniteGammaHom_lift_iso e.hom
    exact congrArg (DirectSum.of (GammaGroundRESKPlus hc ground) k) (gammaGroundRESClass_iso E)
  empty := by
    apply gammaGroundRESDirectSumToRV_injective
    change DirectSum.map (fun _ => gammaGroundRESToRVKPlus)
      (DirectSum.of (GammaGroundRESKPlus hc ground) 0 (gammaGroundRESClass _)) = gammaGroundRESDirectSumToRV 0
    rw [DirectSum.map_of, gammaGroundRESToRVKPlus_class, map_zero]
    change DirectSum.of (GammaGroundRVKPlus hc ground) 0 (gammaGroundRVClass (GammaGroundGammaObject.empty hc ground 0).rvLift) = 0
    rw [gammaGroundGammaRVClass_empty, map_zero]
  unit := by
    apply gammaGroundRESDirectSumToRV_injective
    change DirectSum.map (fun _ => gammaGroundRESToRVKPlus)
      (DirectSum.of (GammaGroundRESKPlus hc ground) 0 (gammaGroundRESClass _)) = gammaGroundRESDirectSumToRV 1
    rw [DirectSum.map_of, gammaGroundRESToRVKPlus_class, gammaGroundRESDirectSumToRV_one]
    change DirectSum.of (GammaGroundRVKPlus hc ground) 0 (gammaGroundRVClass (GammaGroundGammaObject.unit hc ground).rvLift) = _
    rw [gammaGroundGammaRVClass_unit]
    rfl
  product A B := by
    apply gammaGroundRESDirectSumToRV_injective
    rw [gammaGroundRESDirectSumToRV_mul]
    change DirectSum.map (fun _ => gammaGroundRESToRVKPlus)
      (DirectSum.of (GammaGroundRESKPlus hc ground) (A.1 + B.1) (gammaGroundRESClass _)) =
      DirectSum.map (fun _ => gammaGroundRESToRVKPlus) (DirectSum.of (GammaGroundRESKPlus hc ground) A.1 (gammaGroundRESClass _)) *
      DirectSum.map (fun _ => gammaGroundRESToRVKPlus) (DirectSum.of (GammaGroundRESKPlus hc ground) B.1 (gammaGroundRESClass _))
    rw [DirectSum.map_of, DirectSum.map_of, DirectSum.map_of,
      gammaGroundRESToRVKPlus_class, gammaGroundRESToRVKPlus_class, gammaGroundRESToRVKPlus_class, DirectSum.of_mul_of]
    apply congrArg (DirectSum.of (GammaGroundRVKPlus hc ground) (A.1 + B.1))
    exact (gammaGroundGammaRVClass_product A.2.obj B.2.obj).trans (gammaGroundRVClassMul_class _ _).symm
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      have hh : gammaGroundGammaClass a.obj + gammaGroundGammaClass b.obj = gammaGroundGammaClass d.obj + gammaGroundGammaClass e.obj :=
        positiveClass_scissor (gammaGroundGammaPresentation hc ground k) hs
      apply gammaGroundRESDirectSumToRV_injective
      simp only [map_add, gammaGroundRESDirectSumClass, gammaGroundRESDirectSumToRV, DirectSum.map_of, gammaGroundRESToRVKPlus_class]
      rw [← map_add, ← map_add]
      apply congrArg (DirectSum.of (GammaGroundRVKPlus hc ground) k)
      have ht := congrArg gammaGroundGammaToRVKPlus hh
      have ht' : gammaGroundRVClass a.obj.rvLift + gammaGroundRVClass b.obj.rvLift = gammaGroundRVClass d.obj.rvLift + gammaGroundRVClass e.obj.rvLift := by
        simpa only [map_add, gammaGroundGammaToRVKPlus_class] using ht
      exact ht'
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      apply gammaGroundRESDirectSumToRV_injective
      simp only [map_add, gammaGroundRESDirectSumClass, gammaGroundRESDirectSumToRV, DirectSum.map_of, gammaGroundRESToRVKPlus_class]
      change DirectSum.of (GammaGroundRVKPlus hc ground) k (gammaGroundRVClass (GammaGroundGammaObject.empty hc ground k).rvLift) +
        DirectSum.of (GammaGroundRVKPlus hc ground) 0 (gammaGroundRVClass (GammaGroundGammaObject.empty hc ground 0).rvLift) = _
      change DirectSum.of (GammaGroundRVKPlus hc ground) k (gammaGroundRVClass (GammaGroundGammaObject.empty hc ground k).rvLift) +
        DirectSum.of (GammaGroundRVKPlus hc ground) 0 (gammaGroundRVClass (GammaGroundGammaObject.empty hc ground 0).rvLift) =
        DirectSum.of (GammaGroundRVKPlus hc ground) 0 (gammaGroundRVClass (GammaGroundGammaObject.empty hc ground 0).rvLift) +
        DirectSum.of (GammaGroundRVKPlus hc ground) 0 (gammaGroundRVClass (GammaGroundGammaObject.empty hc ground 0).rvLift)
      simp only [gammaGroundGammaRVClass_empty, map_zero, add_zero]

def gammaGroundFiniteGammaToRESSemiring : GammaGroundFiniteGammaPositiveSemiring hc ground →+* GammaGroundRESDirectSum (M := M) hc ground :=
  PositiveGrothendieck.lift (gammaGroundFiniteGammaSemiringPresentation hc ground) gammaGroundFiniteGammaToRESInvariant

@[simp] theorem gammaGroundFiniteGammaToRESSemiring_class (A : GammaGroundFiniteGammaObject hc ground k) :
    gammaGroundFiniteGammaToRESSemiring (gammaGroundFiniteGammaSemiringClass A) = gammaGroundRESDirectSumClass A.resLift :=
  PositiveGrothendieck.lift_of (gammaGroundFiniteGammaSemiringPresentation hc ground) gammaGroundFiniteGammaToRESInvariant ⟨k, A⟩

def gammaGroundRESToRVSemiring : GammaGroundRESDirectSum (M := M) hc ground →+* GammaGroundRVPositiveSemiring hc ground :=
  gammaGroundRVDirectSumToPresentation.comp gammaGroundRESGradedInclusion

@[simp] theorem gammaGroundRESToRVSemiring_class (A : GammaGroundRESObject (M := M) hc ground k) :
    gammaGroundRESToRVSemiring (gammaGroundRESDirectSumClass A) = gammaGroundRVSemiringClass A.obj := by
  change gammaGroundRVDirectSumToPresentation (DirectSum.map (fun _ => gammaGroundRESToRVKPlus)
    (DirectSum.of (GammaGroundRESKPlus hc ground) k (gammaGroundRESClass A))) = _
  rw [DirectSum.map_of, gammaGroundRESToRVKPlus_class]
  exact gammaGroundRVDirectSumToPresentation_class A.obj

theorem gammaGroundRESToRVSemiring_injective : Function.Injective (gammaGroundRESToRVSemiring (M := M) (hc := hc) (ground := ground)) :=
  (gammaGroundRVSemiringEquivDirectSum (M := M) (hc := hc) (ground := ground)).symm.injective.comp gammaGroundRESGradedInclusion_injective

theorem gammaGroundFiniteGamma_semiring_square :
    (gammaGroundRESToRVSemiring (M := M) (hc := hc) (ground := ground)).comp (gammaGroundFiniteGammaToRESSemiring (hc := hc)) =
      gammaGroundGammaToRVSemiring.comp gammaGroundFiniteGammaToGammaSemiring := by
  apply PositiveGrothendieck.hom_ext (gammaGroundFiniteGammaSemiringPresentation hc ground)
  rintro ⟨k, A⟩
  change gammaGroundRESToRVSemiring (gammaGroundFiniteGammaToRESSemiring (gammaGroundFiniteGammaSemiringClass A)) =
    gammaGroundGammaToRVSemiring (gammaGroundFiniteGammaToGammaSemiring (gammaGroundFiniteGammaSemiringClass A))
  rw [gammaGroundFiniteGammaToRESSemiring_class, gammaGroundRESToRVSemiring_class,
    gammaGroundFiniteGammaToGammaSemiring_class, gammaGroundGammaToRVSemiring_class]
  rfl

end DiamondIntegral.Section3
