import «section 6».CarriedMapComposition
import «section 6».CarriedExceptionalSets

/-! Actual finite compositions of relatively unary proper covariant
homeomorphisms with generic unit total derivative. Every intermediate
RV selector is stored, so later carried coordinates remain fixed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

inductive RetainedUnaryHomeChain (S : Set M) :
    {r s : ℕ} → {A : DefSet (rawMixedSpace (M := M) n r) S} →
    {B : DefSet (rawMixedSpace (M := M) n s) S} → Map A B → (Fin r → Fin s) → Type where
  | identity {r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier) :
      RetainedUnaryHomeChain S (Map.id A) id
  | unary {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
      {f : Map A B} {π : Fin r → Fin s} (j : Fin n)
      (home : ProperCovariantHomeomorphism f)
      (relative : ∀ p : A,∀ i,i ≠ j → (f p).val.1 i=p.val.1 i)
      (unit : ∀ p : A,AlgebraicIndependent (vfParameterField S) p.val.1 → HasMixedUnitDerivativeAt f p)
      (retained : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i) : RetainedUnaryHomeChain S f π
  | comp {r s t : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
      {B : DefSet (rawMixedSpace (M := M) n s) S} {C : DefSet (rawMixedSpace (M := M) n t) S}
      {f : Map A B} {g : Map B C} {π : Fin r → Fin s} {σ : Fin s → Fin t}
      (first : RetainedUnaryHomeChain S f π) (second : RetainedUnaryHomeChain S g σ) :
      RetainedUnaryHomeChain S (g.comp f) (σ ∘ π)

namespace RetainedUnaryHomeChain
variable {S : Set M} {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {π : Fin r → Fin s}

def changeMap {g : Map A B} (F : RetainedUnaryHomeChain (G := G) S f π) (he : f=g) :
    RetainedUnaryHomeChain (G := G) S g π := he ▸ F

theorem retained (F : RetainedUnaryHomeChain (G := G) S f π) (p : A) (i : Fin r) :
    (f p).val.2 (π i)=p.val.2 i := by
  induction F with
  | identity A hA => rfl
  | unary j hHome hRelative hUnit hRetain => exact hRetain p i
  | @comp r s t A B C f g π σ first second ihf ihg =>
    exact (ihg (f p) (π i)).trans (ihf p i)

theorem bijective (F : RetainedUnaryHomeChain (G := G) S f π) : Function.Bijective f := by
  induction F with
  | identity A hA => exact Function.bijective_id
  | unary j hHome hRelative hUnit hRetain => exact hHome.bijective
  | comp first second ihf ihg => exact ihg.comp ihf

theorem homeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : RetainedUnaryHomeChain (G := G) S f π) : ProperCovariantHomeomorphism f := by
  induction F with
  | identity A hA => exact identity_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ hA
  | unary j hHome hRelative hUnit hRetain => exact hHome
  | comp first second ihf ihg => exact lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ ihf ihg

theorem generic_unit (hc : CanonicalStructure.IsCanonical (M := M))
    (F : RetainedUnaryHomeChain (G := G) S f π) (p : A)
    (hInd : AlgebraicIndependent (vfParameterField S) p.val.1) : HasMixedUnitDerivativeAt f p := by
  induction F with
  | identity A hA => exact identity_unit_derivative hA p
  | unary j hHome hRelative hUnit hRetain => exact hUnit p hInd
  | comp first second ihf ihg =>
    exact (ihg _ (independent_map_of_finiteFibres hc _ (Map.finiteFibres_of_injective first.bijective.injective) p hInd)).comp
      (ihf p hInd)

end RetainedUnaryHomeChain
end DiamondIntegral.Section6
