import «section 3».FiniteGammaSemiring
import «section 3».GammaSemiringLift
import «section 3».RESGradedSemiring

/-! The actual unmeasured coefficient square, including multiplication. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def finiteGammaToGammaInvariant : PositiveGrothendieck.Invariant
    (finiteGammaSemiringPresentation hc S) (R := GammaPositiveSemiring hc S) where
  toFun A := gammaSemiringClass A.2.obj
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact gammaSemiringClass_iso ((finiteGammaProperty (hc := hc) (S := S) (k := k)).ι.mapIso e)
  empty := gammaSemiringClass_empty
  unit := gammaSemiringClass_unit
  product A B := gammaSemiringClass_product A.2.obj B.2.obj
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      exact gammaSemiringClass_scissor hs
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      simp only [FiniteGammaObject.empty, gammaSemiringClass_empty, add_zero]

def finiteGammaToGammaSemiring : FiniteGammaPositiveSemiring hc S →+* GammaPositiveSemiring hc S :=
  PositiveGrothendieck.lift (finiteGammaSemiringPresentation hc S) finiteGammaToGammaInvariant

@[simp] theorem finiteGammaToGammaSemiring_class (A : FiniteGammaObject hc S k) :
    finiteGammaToGammaSemiring (finiteGammaSemiringClass A) = gammaSemiringClass A.obj :=
  PositiveGrothendieck.lift_of (finiteGammaSemiringPresentation hc S) finiteGammaToGammaInvariant ⟨k, A⟩

def finiteGammaToRESInvariant : PositiveGrothendieck.Invariant
    (finiteGammaSemiringPresentation hc S) (R := RESDirectSum (M := M) S) where
  toFun A := resDirectSumClass A.2.resLift
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    obtain ⟨E⟩ := finiteGammaHom_lift_iso e.hom
    exact congrArg (DirectSum.of (RESKPlus S) k) (resClass_iso E)
  empty := by
    apply resDirectSumToRV_injective
    change DirectSum.map (fun _ => resToRVKPlus)
      (DirectSum.of (RESKPlus S) 0 (resClass _)) = resDirectSumToRV 0
    rw [DirectSum.map_of, resToRVKPlus_class, map_zero]
    change DirectSum.of (RVKPlus S) 0 (rvClass (GammaObject.empty hc S 0).rvLift) = 0
    rw [gammaRVClass_empty, map_zero]
  unit := by
    apply resDirectSumToRV_injective
    change DirectSum.map (fun _ => resToRVKPlus)
      (DirectSum.of (RESKPlus S) 0 (resClass _)) = resDirectSumToRV 1
    rw [DirectSum.map_of, resToRVKPlus_class, resDirectSumToRV_one]
    change DirectSum.of (RVKPlus S) 0 (rvClass (GammaObject.unit hc S).rvLift) = _
    rw [gammaRVClass_unit]
    rfl
  product A B := by
    apply resDirectSumToRV_injective
    rw [resDirectSumToRV_mul]
    change DirectSum.map (fun _ => resToRVKPlus)
      (DirectSum.of (RESKPlus S) (A.1 + B.1) (resClass _)) =
      DirectSum.map (fun _ => resToRVKPlus) (DirectSum.of (RESKPlus S) A.1 (resClass _)) *
      DirectSum.map (fun _ => resToRVKPlus) (DirectSum.of (RESKPlus S) B.1 (resClass _))
    rw [DirectSum.map_of, DirectSum.map_of, DirectSum.map_of,
      resToRVKPlus_class, resToRVKPlus_class, resToRVKPlus_class, DirectSum.of_mul_of]
    apply congrArg (DirectSum.of (RVKPlus S) (A.1 + B.1))
    exact (gammaRVClass_product A.2.obj B.2.obj).trans (rvClassMul_class _ _).symm
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      have hh : gammaClass a.obj + gammaClass b.obj = gammaClass d.obj + gammaClass e.obj :=
        positiveClass_scissor (gammaPresentation hc S k) hs
      apply resDirectSumToRV_injective
      simp only [map_add, resDirectSumClass, resDirectSumToRV, DirectSum.map_of, resToRVKPlus_class]
      rw [← map_add, ← map_add]
      apply congrArg (DirectSum.of (RVKPlus S) k)
      have ht := congrArg gammaToRVKPlus hh
      have ht' : rvClass a.obj.rvLift + rvClass b.obj.rvLift = rvClass d.obj.rvLift + rvClass e.obj.rvLift := by
        simpa only [map_add, gammaToRVKPlus_class] using ht
      exact ht'
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      apply resDirectSumToRV_injective
      simp only [map_add, resDirectSumClass, resDirectSumToRV, DirectSum.map_of, resToRVKPlus_class]
      change DirectSum.of (RVKPlus S) k (rvClass (GammaObject.empty hc S k).rvLift) +
        DirectSum.of (RVKPlus S) 0 (rvClass (GammaObject.empty hc S 0).rvLift) = _
      change DirectSum.of (RVKPlus S) k (rvClass (GammaObject.empty hc S k).rvLift) +
        DirectSum.of (RVKPlus S) 0 (rvClass (GammaObject.empty hc S 0).rvLift) =
        DirectSum.of (RVKPlus S) 0 (rvClass (GammaObject.empty hc S 0).rvLift) +
        DirectSum.of (RVKPlus S) 0 (rvClass (GammaObject.empty hc S 0).rvLift)
      simp only [gammaRVClass_empty, map_zero, add_zero]

def finiteGammaToRESSemiring : FiniteGammaPositiveSemiring hc S →+* RESDirectSum (M := M) S :=
  PositiveGrothendieck.lift (finiteGammaSemiringPresentation hc S) finiteGammaToRESInvariant

@[simp] theorem finiteGammaToRESSemiring_class (A : FiniteGammaObject hc S k) :
    finiteGammaToRESSemiring (finiteGammaSemiringClass A) = resDirectSumClass A.resLift :=
  PositiveGrothendieck.lift_of (finiteGammaSemiringPresentation hc S) finiteGammaToRESInvariant ⟨k, A⟩

def resToRVSemiring : RESDirectSum (M := M) S →+* RVPositiveSemiring S :=
  rvDirectSumToPresentation.comp resGradedInclusion

@[simp] theorem resToRVSemiring_class (A : RESObject (M := M) S k) :
    resToRVSemiring (resDirectSumClass A) = rvSemiringClass A.obj := by
  change rvDirectSumToPresentation (DirectSum.map (fun _ => resToRVKPlus)
    (DirectSum.of (RESKPlus S) k (resClass A))) = _
  rw [DirectSum.map_of, resToRVKPlus_class]
  exact rvDirectSumToPresentation_class A.obj

theorem resToRVSemiring_injective : Function.Injective (resToRVSemiring (M := M) (S := S)) :=
  (rvSemiringEquivDirectSum (M := M) (S := S)).symm.injective.comp resGradedInclusion_injective

theorem finiteGamma_semiring_square :
    (resToRVSemiring (M := M) (S := S)).comp (finiteGammaToRESSemiring (hc := hc)) =
      gammaToRVSemiring.comp finiteGammaToGammaSemiring := by
  apply PositiveGrothendieck.hom_ext (finiteGammaSemiringPresentation hc S)
  rintro ⟨k, A⟩
  change resToRVSemiring (finiteGammaToRESSemiring (finiteGammaSemiringClass A)) =
    gammaToRVSemiring (finiteGammaToGammaSemiring (finiteGammaSemiringClass A))
  rw [finiteGammaToRESSemiring_class, resToRVSemiring_class,
    finiteGammaToGammaSemiring_class, gammaToRVSemiring_class]
  rfl

end DiamondIntegral.Section3
