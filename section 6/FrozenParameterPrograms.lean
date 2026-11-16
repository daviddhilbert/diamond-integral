import «section 6».CentripetalProgramSubstitution
import «section 6».UncurriedMixedTemplates
import «section 6».ContinuousFocusFreezing
import «section 6».RootFreezingGeometry

/-! Actual finite-disc freezing substitutes the parameter in the
whole finite program. Product checks on its initial ambient and
protected pieces preserve those full sources; every later domain and
focus is recomputed by the substituted program. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}

namespace FMT

def freezingParameterSubstitution
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M)
    (hSep : ∀ D E : balls,∀ x,x ∈ OpenBallCodes.underlying D.val → x ∈ OpenBallCodes.underlying E.val → D=E)
    (hBalls : S.Definable LRV (OpenBallCodes.pullback balls))
    (hCenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val))) :
    DefinableParameterSubstitution (M := M) S 1 1 :=
  ⟨(fun a _ => rawFamilyFreeze balls centers (a 0)),fun _ => rawFamilyFreeze_definable balls centers hSep hBalls hCenters⟩

theorem freezingParameterSubstitution_at
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M)
    (hSep : ∀ D E : balls,∀ x,x ∈ OpenBallCodes.underlying D.val → x ∈ OpenBallCodes.underlying E.val → D=E)
    (hBalls : S.Definable LRV (OpenBallCodes.pullback balls))
    (hCenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    (a : VF M) :
    (freezingParameterSubstitution balls centers hSep hBalls hCenters).value (fun _ => a.val)=
      (fun _ => (vfFamilyFreeze balls centers a).val) := rfl

theorem uncurry_substituted_head_source
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M)
    (hSep : ∀ D E : balls,∀ x,x ∈ OpenBallCodes.underlying D.val → x ∈ OpenBallCodes.underlying E.val → D=E)
    (hBalls : S.Definable LRV (OpenBallCodes.pullback balls))
    (hCenters : S.Definable LRV (OpenBallCodes.quotientCenterGraph balls (fun D => (centers D).val)))
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hProd : ∀ D : balls,CoordinateProductDomain A.carrier (vfOpenBall D.val) (centers D) 0) :
    ((headFibreTemplate A).substitute (freezingParameterSubstitution balls centers hSep hBalls hCenters)).uncurry=A := by
  apply defSet_eq_of_carrier_eq
  ext p
  rw [MixedSetParameterTemplate.mem_uncurry_iff,MixedSetParameterTemplate.substitute_carrier,
    freezingParameterSubstitution_at,mem_headFibreTemplate_iff]
  have hPoint : (Fin.cons (vfFamilyFreeze balls centers (p.1 0)) (Fin.tail p.1),p.2)=
      mixedFamilyFreeze balls centers 0 p := by
    apply Prod.ext
    · funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · rfl
      · simp only [Fin.cons_succ,mixedFamilyFreeze,Function.update_of_ne (Fin.succ_ne_zero i)]
        rfl
    · rfl
  rw [hPoint]
  exact mixedFamilyFreeze_mem_iff balls centers 0 hSep A.carrier hProd p

end FMT
end DiamondIntegral.Section6
