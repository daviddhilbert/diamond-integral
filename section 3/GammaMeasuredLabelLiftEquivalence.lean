import «section 3».GammaFullLabelDescent
import «section 3».GammaMeasuredHomLiftClosure

/-! The exact Gamma-valued label-compatible lifting comparison, in both
directions. Gamma density functions remain arbitrary throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMeasured_label_lift_iff
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hB : VFGammaGeneratedBase (closureBase B))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U V : GammaGroundMeasuredRVObject hc B k)
    (e : GammaGroundBijection U.underlying.domain V.underlying.domain) :
    (∀ u, U.combinedWeight u = V.combinedWeight (e.map u)) ↔
    ∃ f : GammaGroundBijection (gammaGroundObjectLift U.underlying) (gammaGroundObjectLift V.underlying),
      (∀ p, gammaGroundObjectLiftLabel V.underlying (f.map p) =
        e.map (gammaGroundObjectLiftLabel U.underlying p)) ∧
      ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
        ∃ J : Section2.VF M, HasMixedVFJacobianAt f.map p J ∧
          gammaGroundMeasuredVFWeight (gammaGroundMeasuredObjectLift U) p =
            gammaGroundMeasuredVFWeight (gammaGroundMeasuredObjectLift V) (f.map p) * Values.vfValueHom J := by
  constructor
  · intro h
    exact gammaMeasuredHom_lift_bijection_closure hκ hs h00 hr hg hB hv
      (show GammaGroundMeasuredRVHom U V from ⟨e,h⟩)
  · rintro ⟨f,hl,hm⟩
    exact gammaFullLabelDescent hκ hs h00 hr U V e f hl hm

end DiamondIntegral.Section3
