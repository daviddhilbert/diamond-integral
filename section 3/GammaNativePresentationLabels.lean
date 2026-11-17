import «section 3».GammaMeasuredPresentationIsomorphism

/-! The actual Gamma presentation isomorphism recovers precisely the
old-label tail of a full RV key. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaNativePresentation_old_labels (U : GammaObjectAt B Set.univ (n+1))
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ (n+1) U.object.obj (normalizedPointSet A))
    (hA : GammaSetDefinable B (carrier A))
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaPresentationAt U h hA)) :
    ((Section5.nativeRVGroundIso (gammaPresentationIsoAt U h hA)).map u).val =
      u.val ∘ Fin.natAdd (n+1) :=
  pullbackPresentationIso_labels h (Section5.nativeRVGroundDomainEquiv (gammaPresentationAt U h hA) u)

end DiamondIntegral.Section3
