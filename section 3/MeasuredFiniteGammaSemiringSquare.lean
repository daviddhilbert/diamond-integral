import «section 3».MeasuredFiniteGammaSemiring
import «section 3».MeasuredGammaSemiringLift
import «section 3».MeasuredRESGradedSemiring
import «section 3».MeasuredFiniteGammaSquare
import «section 3».MeasuredRVGradedComparison

/-! The actual measured coefficient square, including multiplication. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def measuredFiniteGammaToGammaInvariant : PositiveGrothendieck.Invariant
    (measuredFiniteGammaSemiringPresentation hc S) (R := MeasuredGammaPositiveSemiring hc S) where
  toFun A := measuredGammaSemiringClass A.2.obj
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact measuredGammaSemiringClass_iso ((measuredFiniteGammaProperty (hc := hc) (S := S) (k := k)).ι.mapIso e)
  empty := measuredGammaSemiringClass_empty
  unit := measuredGammaSemiringClass_unit
  product A B := measuredGammaSemiringClass_product A.2.obj B.2.obj
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      exact measuredGammaSemiringClass_scissor hs
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      simp only [MeasuredFiniteGammaObject.empty, measuredGammaSemiringClass_empty, add_zero]

def measuredFiniteGammaToGammaSemiring : MeasuredFiniteGammaPositiveSemiring hc S →+* MeasuredGammaPositiveSemiring hc S :=
  PositiveGrothendieck.lift (measuredFiniteGammaSemiringPresentation hc S) measuredFiniteGammaToGammaInvariant

@[simp] theorem measuredFiniteGammaToGammaSemiring_class (A : MeasuredFiniteGammaObject hc S k) :
    measuredFiniteGammaToGammaSemiring (measuredFiniteGammaSemiringClass A) = measuredGammaSemiringClass A.obj :=
  PositiveGrothendieck.lift_of (measuredFiniteGammaSemiringPresentation hc S) measuredFiniteGammaToGammaInvariant ⟨k, A⟩

def measuredFiniteGammaToRESInvariant : PositiveGrothendieck.Invariant
    (measuredFiniteGammaSemiringPresentation hc S) (R := MeasuredRESDirectSum (M := M) hc S) where
  toFun A := measuredResDirectSumClass hc A.2.resLift
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    obtain ⟨E⟩ := measuredFiniteGammaHom_lift_iso e.hom
    exact congrArg (DirectSum.of (MeasuredRESKPlus hc S) k) (measuredResClass_iso hc E)
  empty := by
    apply measuredResDirectSumToRV_injective
    change DirectSum.map (fun _ => measuredResToRVKPlus hc)
      (DirectSum.of (MeasuredRESKPlus hc S) 0 (measuredResClass hc _)) = measuredResDirectSumToRV 0
    rw [DirectSum.map_of, measuredResToRVKPlus_class hc, map_zero]
    change DirectSum.of (MeasuredRVKPlus hc S) 0 (measuredRVClass hc (MeasuredGammaObject.empty hc S 0).rvLift) = 0
    rw [measuredGammaRVClass_empty, map_zero]
  unit := by
    apply measuredResDirectSumToRV_injective
    change DirectSum.map (fun _ => measuredResToRVKPlus hc)
      (DirectSum.of (MeasuredRESKPlus hc S) 0 (measuredResClass hc _)) = measuredResDirectSumToRV 1
    rw [DirectSum.map_of, measuredResToRVKPlus_class hc, measuredResDirectSumToRV_one]
    change DirectSum.of (MeasuredRVKPlus hc S) 0 (measuredRVClass hc (MeasuredGammaObject.unit hc S).rvLift) = _
    rw [measuredGammaRVClass_unit]
    rfl
  product A B := by
    apply measuredResDirectSumToRV_injective
    rw [measuredResDirectSumToRV_mul]
    change DirectSum.map (fun _ => measuredResToRVKPlus hc)
      (DirectSum.of (MeasuredRESKPlus hc S) (A.1 + B.1) (measuredResClass hc _)) =
      DirectSum.map (fun _ => measuredResToRVKPlus hc) (DirectSum.of (MeasuredRESKPlus hc S) A.1 (measuredResClass hc _)) *
      DirectSum.map (fun _ => measuredResToRVKPlus hc) (DirectSum.of (MeasuredRESKPlus hc S) B.1 (measuredResClass hc _))
    rw [DirectSum.map_of, DirectSum.map_of, DirectSum.map_of,
      measuredResToRVKPlus_class hc, measuredResToRVKPlus_class hc, measuredResToRVKPlus_class hc, DirectSum.of_mul_of]
    apply congrArg (DirectSum.of (MeasuredRVKPlus hc S) (A.1 + B.1))
    exact (measuredGammaRVClass_product A.2.obj B.2.obj).trans (measuredRVClassMul_class _ _).symm
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      have hh : measuredGammaClass a.obj + measuredGammaClass b.obj = measuredGammaClass d.obj + measuredGammaClass e.obj :=
        positiveClass_scissor (measuredGammaPresentation hc S k) hs
      apply measuredResDirectSumToRV_injective
      simp only [map_add, measuredResDirectSumClass, measuredResDirectSumToRV, DirectSum.map_of, measuredResToRVKPlus_class hc]
      rw [← map_add, ← map_add]
      apply congrArg (DirectSum.of (MeasuredRVKPlus hc S) k)
      have ht := congrArg measuredGammaToRVKPlus hh
      have ht' : measuredRVClass hc a.obj.rvLift + measuredRVClass hc b.obj.rvLift = measuredRVClass hc d.obj.rvLift + measuredRVClass hc e.obj.rvLift := by
        simpa only [map_add, measuredGammaToRVKPlus_class] using ht
      exact ht'
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      apply measuredResDirectSumToRV_injective
      simp only [map_add, measuredResDirectSumClass, measuredResDirectSumToRV, DirectSum.map_of, measuredResToRVKPlus_class hc]
      change DirectSum.of (MeasuredRVKPlus hc S) k (measuredRVClass hc (MeasuredGammaObject.empty hc S k).rvLift) +
        DirectSum.of (MeasuredRVKPlus hc S) 0 (measuredRVClass hc (MeasuredGammaObject.empty hc S 0).rvLift) = _
      change DirectSum.of (MeasuredRVKPlus hc S) k (measuredRVClass hc (MeasuredGammaObject.empty hc S k).rvLift) +
        DirectSum.of (MeasuredRVKPlus hc S) 0 (measuredRVClass hc (MeasuredGammaObject.empty hc S 0).rvLift) =
        DirectSum.of (MeasuredRVKPlus hc S) 0 (measuredRVClass hc (MeasuredGammaObject.empty hc S 0).rvLift) +
        DirectSum.of (MeasuredRVKPlus hc S) 0 (measuredRVClass hc (MeasuredGammaObject.empty hc S 0).rvLift)
      simp only [measuredGammaRVClass_empty, map_zero, add_zero]

def measuredFiniteGammaToRESSemiring : MeasuredFiniteGammaPositiveSemiring hc S →+* MeasuredRESDirectSum (M := M) hc S :=
  PositiveGrothendieck.lift (measuredFiniteGammaSemiringPresentation hc S) measuredFiniteGammaToRESInvariant

@[simp] theorem measuredFiniteGammaToRESSemiring_class (A : MeasuredFiniteGammaObject hc S k) :
    measuredFiniteGammaToRESSemiring (measuredFiniteGammaSemiringClass A) = measuredResDirectSumClass hc A.resLift :=
  PositiveGrothendieck.lift_of (measuredFiniteGammaSemiringPresentation hc S) measuredFiniteGammaToRESInvariant ⟨k, A⟩

def measuredResToRVSemiring : MeasuredRESDirectSum (M := M) hc S →+* MeasuredRVPositiveSemiring hc S :=
  measuredRVDirectSumToPresentation.comp measuredResGradedInclusion

@[simp] theorem measuredResToRVSemiring_class (A : MeasuredRESObject (M := M) S k) :
    measuredResToRVSemiring (measuredResDirectSumClass hc A) = measuredRVSemiringClass hc A.obj := by
  change measuredRVDirectSumToPresentation (DirectSum.map (fun _ => measuredResToRVKPlus hc)
    (DirectSum.of (MeasuredRESKPlus hc S) k (measuredResClass hc A))) = _
  rw [DirectSum.map_of, measuredResToRVKPlus_class hc]
  exact measuredRVDirectSumToPresentation_class A.obj

theorem measuredResToRVSemiring_injective : Function.Injective (measuredResToRVSemiring (M := M) (S := S) (hc := hc)) :=
  (measuredRVSemiringEquivDirectSum (M := M) (S := S) (hc := hc)).symm.injective.comp measuredResGradedInclusion_injective

theorem measuredFiniteGamma_semiring_square :
    (measuredResToRVSemiring (M := M) (S := S) (hc := hc)).comp (measuredFiniteGammaToRESSemiring (hc := hc)) =
      measuredGammaToRVSemiring.comp measuredFiniteGammaToGammaSemiring := by
  apply PositiveGrothendieck.hom_ext (measuredFiniteGammaSemiringPresentation hc S)
  rintro ⟨k, A⟩
  change measuredResToRVSemiring (measuredFiniteGammaToRESSemiring (measuredFiniteGammaSemiringClass A)) =
    measuredGammaToRVSemiring (measuredFiniteGammaToGammaSemiring (measuredFiniteGammaSemiringClass A))
  rw [measuredFiniteGammaToRESSemiring_class, measuredResToRVSemiring_class,
    measuredFiniteGammaToGammaSemiring_class, measuredGammaToRVSemiring_class]
  rfl

end DiamondIntegral.Section3
