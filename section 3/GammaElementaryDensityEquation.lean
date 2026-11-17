import «section 3».GammaElementaryLiftJacobian
import Integration7.CanonicalFocusLiftVolumeMaps

/-! The elementary focus retains every original RV label. Thus the same
actual lift transports every Gamma density, including densities that have
no definable RV representative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7 SpecialTransformations.Section9
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem gammaElementaryLift_original_labels {U : GammaRVObject B n} {i : Fin n}
    (D : ElementaryLiftDiagram U i) (p : typedLift U.object) :
    (D.liftIso.equiv p).val.2 ∘ Fin.castAdd 1 = p.val.2 :=
  IntegrationInACVF.Section7.canonical_focus_lift_original_labels
    (normalizedTypedLift_presents U.object) D.focus D.full.ge D.admissible p

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaElementaryLift_density_equation
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U : GammaRVObject B n} {i : Fin n} (D : ElementaryLiftDiagram U i)
    (ω : (Fin (rvObjectArity U.object) → CanonicalRV.RVSort M) → Values.GammaTop (M := M))
    (p : typedLift U.object)
    (hp : AlgebraicIndependent (vfParameterField B.real) (show Fin n → Section2.VF M from p.val.1)) :
    ∃ J : Section2.VF M, HasMixedVFJacobianAt D.liftIso.equiv p J ∧
      ω p.val.2 = ω ((D.liftIso.equiv p).val.2 ∘ Fin.castAdd 1) * Values.vfValueHom J := by
  refine ⟨1,gammaElementaryLift_jacobian_one hc hκ hs hr hv D p hp,?_⟩
  rw [map_one,mul_one,gammaElementaryLift_original_labels]

end DiamondIntegral.Section3
