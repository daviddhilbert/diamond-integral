import «section 4».GammaCounterweightedRay
import «section 4».GammaPointFamilies
import «section 4».GammaUnboundedSpecialization
import «section 4».GammaObjectPolynomial

/-! With constant zero volume, a unary Gamma object's corrected-weight
pushforward is its actual indicator function. In particular the positive
ray has profile q_0 for both Euler theories. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaUnaryIdentityProfile
open GammaDefinableEuler GammaOrderLogic GammaDefinableMaps GammaIntegerFamilies
open GammaHigherPushforward GammaWeightProfiles GammaPointFamilies GammaIteratedIntegral
open GammaParameterExtension GammaCounterweightedRay GammaObjectPolynomial EulerFunction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem pushforward_coordinate (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (T : (Fin 1 → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (hcoord : ∀ z, T z = z 0) (f : familySubgroup B 1) :
    (pushforward h00 hκ hs B hr hγ k T hT f).val = (GammaUnaryFamilyBridge.toEuler h00 B k f).val := by
  apply eval_injective k
  funext x
  obtain ⟨a, rfl⟩ := toPaperGamma.surjective x
  change (pushforward h00 hκ hs B hr hγ k T hT f).val (toPaperGamma a) =
    (GammaUnaryFamilyBridge.toEuler h00 B k f).val (toPaperGamma a)
  rw [pushforward_eval, GammaUnaryFamilyBridge.toEuler_eval]
  apply integrateAll_singleton h00 hκ hs (GammaBaseExtension.withGamma B (Set.range ![a])) hr
    (finite_gamma_extension_small hκ B hγ ![a]) k 1 _ ![a] (f.val ![a])
  intro z
  rw [fibreFamily_eval, hcoord]
  by_cases hz : z 0 = a
  · have he : z = ![a] := by funext i; fin_cases i; exact hz
    subst z
    simp
  · have he : z ≠ ![a] := fun h => hz (congrFun h 0)
    simp [hz, he]

theorem profile_one (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (I : Set (Fin 1 → Values.Gamma (M := M))) (hI : GammaDefinable B I) :
    (profile h00 hκ hs B hr hγ k I hI (fun _ => 1)
      (constant_definable B 1 (GammaGroupNames.one_definable_base B))).val =
      (GammaUnaryFamilyBridge.toEuler h00 B k (GammaIndicators.indicatorFamily B I hI)).val := by
  unfold profile
  apply pushforward_coordinate
  intro z
  simp [correctedWeight]

theorem profile_positiveRay (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (k : EulerKind) :
    (profile h00 hκ hs B hr hγ k positiveRay (positiveRay_definable B) (fun _ => 1)
      (constant_definable B 1 (GammaGroupNames.one_definable_base B))).val = ray k 0 := by
  rw [profile_one]
  apply eval_injective k
  funext x
  obtain ⟨a, rfl⟩ := toPaperGamma.surjective x
  change (GammaUnaryFamilyBridge.toEuler h00 B k
    (GammaIndicators.indicatorFamily B positiveRay (positiveRay_definable B))).val (toPaperGamma a) =
      ray k 0 (toPaperGamma a)
  rw [GammaUnaryFamilyBridge.toEuler_eval, ray_eval]
  by_cases ha : (1 : Values.Gamma (M := M)) < a
  · have hp : (0 : PaperGamma (M := M)) < toPaperGamma a := ha
    simp [GammaIndicators.indicatorFamily, positiveRay, ha, hp]
  · have hp : ¬ (0 : PaperGamma (M := M)) < toPaperGamma a := ha
    simp [GammaIndicators.indicatorFamily, positiveRay, ha, hp]

theorem objectPolynomial_positiveRay (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (k : EulerKind) :
    objectPolynomial h00 hκ hs B hr hγ k 1 positiveRay (positiveRay_definable B) (fun _ => 1)
      (constant_definable B 1 (GammaGroupNames.one_definable_base B)) =
      GammaUnboundedSpecialization.rayMonomial B k 1 (by decide) 0 := by
  apply Subtype.ext
  apply congrArg (Polynomial.monomial 1)
  apply Subtype.ext
  exact profile_positiveRay h00 hκ hs B hr hγ k

end DiamondIntegral.Section4.GammaUnaryIdentityProfile
