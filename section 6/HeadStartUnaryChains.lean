import «section 6».CarriedUnaryHomeChains
import «section 6».HeadStartCarriedBijections

/-! Adding any selected block of retained RV labels carries each actual
relatively unary step. Every added VF coordinate is fixed, and the
result is the actual recursively defined head-start bijection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {f : Map A B} {σ : Fin r → Fin s}

def RetainedUnaryHomeChain.carryHeadStart
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : RetainedUnaryHomeChain (G := G) S f σ) :
    (k : ℕ) → (π : Fin k → Fin r) →
    RetainedUnaryHomeChain (G := G) S
      (carryHeadStartBijection f F.bijective k π (σ ∘ π) (fun p i => F.retained p (π i))).map σ := by
  intro k
  induction k with
  | zero =>
    intro π
    exact F
  | succ k ih =>
    intro π
    exact (ih (π ∘ Fin.castSucc)).carryLast h00 hc linear hκ hs hv hsmall hΓ (π (Fin.last k))

end DiamondIntegral.Section6
