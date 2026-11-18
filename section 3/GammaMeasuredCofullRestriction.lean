import «section 3».GammaMeasuredArrowLift

/-! Discarding a definable lower-dimensional subset preserves the
actual measured VF class, with the original density restricted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def gammaMeasuredCofullRestrictionHom (U : GammaGroundMeasuredVFData hc B (n+1))
    (E : GammaGroundDefSet hc B (rawMixedSpace (M := M) (n+1) U.arity))
    (hE : E.carrier ⊆ U.domain.carrier)
    (hsmall : Section2.vfDimension (U.domain.sdiff E).carrier < ((n+1 : ℕ) : WithBot ℕ)) :
    GammaGroundMeasuredVFHom hκ hs hr hv U (U.restrict E hE) := by
  let F : GammaGroundEssentialVFMap U.domain E := {
    source := E
    target := E
    source_subset := hE
    target_subset := Set.Subset.refl _
    source_small := hsmall
    target_small := by rw [show (E.sdiff E).carrier = ∅ from Set.sdiff_self,Section2.vfDimension_empty]; exact WithBot.bot_lt_coe _
    map := GammaGroundMap.id E
    bijective := Function.bijective_id }
  have hF : F.PreservesGeneric Values.vfValueHom (gammaGroundMeasuredVFWeight U)
      (gammaGroundMeasuredVFWeight (U.restrict E hE)) :=
    GammaGroundEssentialVFMap.preservesGeneric_id hκ hs hr hv Values.vfValueHom
      (gammaGroundMeasuredVFWeight (U.restrict E hE))
  exact (gammaGroundMeasuredGermEquivGeneric hκ hs hr hv (Nat.zero_lt_succ n) U (U.restrict E hE)).symm
    ⟨F.genericEquiv hκ hs hr hv (Nat.zero_lt_succ n),F,hF,rfl⟩

end DiamondIntegral.Section3
