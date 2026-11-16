import «section 6».RestrictionSourceTransport

/-! One common finite chain with compatible permitted component data
on every protected piece. This retains a single ambient construction
while certifying all literal restrictions simultaneously. -/

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

inductive SimultaneousCentripetalChain (I : Type*) : {r s : ℕ} →
    (A : DefSet (rawMixedSpace (M := M) n r) S) →
    (B : DefSet (rawMixedSpace (M := M) n s) S) → Map A B →
    (I → DefSet (rawMixedSpace (M := M) n r) S) → Prop where
  | identity (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i, (P i).carrier ⊆ A.carrier)
      (hP : ∀ i, ProperInvariant S (P i).carrier) : SimultaneousCentripetalChain I A A (Map.id A) P
  | regularize (A : DefSet (rawMixedSpace (M := M) n r) S)
      (hA : ProperInvariant S A.carrier) (hVF : VFDoublyBounded A.carrier)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i, (P i).carrier ⊆ A.carrier)
      (hP : ∀ i, ProperInvariant S (P i).carrier) (hPVF : ∀ i, VFDoublyBounded (P i).carrier) :
      SimultaneousCentripetalChain I A (regularizeMap A).image (regularization A) P
  | centripetal (A : DefSet (rawMixedSpace (M := M) n r) S) (D : CentripetalData (G := G) A)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i, (P i).carrier ⊆ A.carrier)
      (E : ∀ i, CentripetalData (G := G) (P i))
      (hPoint : ∀ i, ∀ p ∈ (P i).carrier, (E i).point p = D.point p) :
      SimultaneousCentripetalChain I A D.map.image D.bijection P
  | comp {A : DefSet (rawMixedSpace (M := M) n r) S}
      {B : DefSet (rawMixedSpace (M := M) n s) S}
      {C : DefSet (rawMixedSpace (M := M) n t) S} {f : Map A B} {g : Map B C}
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i, (P i).carrier ⊆ A.carrier)
      (hf : SimultaneousCentripetalChain I A B f P)
      (hg : SimultaneousCentripetalChain I B C g (fun i => (f.restrict (hPA i)).image)) :
      SimultaneousCentripetalChain I A C (g.comp f) P

theorem SimultaneousCentripetalChain.toChain {I : Type*} {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SimultaneousCentripetalChain (G := G) I A B f P) : CentripetalChain (G := G) A B f := by
  induction h with
  | identity A hA P hPA hP => exact .identity A hA
  | regularize A hA hVF P hPA hP hPVF => exact .regularize A hA hVF
  | centripetal A D P hPA E hPoint => exact .centripetal A D
  | comp P hPA hf hg ihf ihg => exact .comp ihf ihg

theorem SimultaneousCentripetalChain.atPiece {I : Type*} {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SimultaneousCentripetalChain (G := G) I A B f P) :
    ∀ i, CompatibleCentripetalChain (G := G) A B f (P i) := by
  induction h with
  | identity A hA P hPA hP => intro i; exact .identity A hA (P i) (hPA i) (hP i)
  | regularize A hA hVF P hPA hP hPVF => intro i; exact .regularize A hA hVF (P i) (hPA i) (hP i) (hPVF i)
  | centripetal A D P hPA E hPoint => intro i; exact .centripetal A D (P i) (hPA i) (E i) (hPoint i)
  | comp P hPA hf hg ihf ihg => intro i; exact .comp (P i) (hPA i) (ihf i) (ihg i)

end DiamondIntegral.Section6
