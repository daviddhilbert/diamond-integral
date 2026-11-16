import «section 6».CarriedRefinementFrames

/-! Finite chains of the permitted centripetal components and actual
regularizations, after preliminary zero-centered preparation. These
are literal SpecialCovariantChains; no new operation is admitted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

inductive CentripetalChain : {r s : ℕ} →
    (A : DefSet (rawMixedSpace (M := M) n r) S) →
    (B : DefSet (rawMixedSpace (M := M) n s) S) → Map A B → Prop where
  | identity (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier) :
      CentripetalChain A A (Map.id A)
  | regularize (A : DefSet (rawMixedSpace (M := M) n r) S)
      (hA : ProperInvariant S A.carrier) (hVF : VFDoublyBounded A.carrier) :
      CentripetalChain A (regularizeMap A).image (regularization A)
  | centripetal (A : DefSet (rawMixedSpace (M := M) n r) S) (D : CentripetalData (G := G) A) :
      CentripetalChain A D.map.image D.bijection
  | comp {A : DefSet (rawMixedSpace (M := M) n r) S}
      {B : DefSet (rawMixedSpace (M := M) n s) S}
      {C : DefSet (rawMixedSpace (M := M) n t) S}
      {f : Map A B} {g : Map B C}
      (hf : CentripetalChain A B f) (hg : CentripetalChain B C g) :
      CentripetalChain A C (g.comp f)

theorem CentripetalChain.toSpecial {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} (h : CentripetalChain (G := G) A B f) : SpecialCovariantChain (G := G) A B f := by
  induction h with
  | identity A hA => exact .identity A hA
  | regularize A hA hVF => exact .regularize A hA hVF
  | centripetal A D => exact .centripetal A D
  | comp hf hg ihf ihg => exact .comp ihf ihg

def changeMapTarget {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B C : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B) (h : B = C) : Map A C := h ▸ f

theorem changeMapTarget_value {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B C : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B) (h : B = C) (p : A) :
    (changeMapTarget f h p).val = (f p).val := by
  cases h
  rfl

end DiamondIntegral.Section6
