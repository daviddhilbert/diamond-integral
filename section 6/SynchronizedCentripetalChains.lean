import «section 6».SimultaneousFocusSteps

/-! A common finite chain retaining the actual coordinate, coefficient
and focus compatibility on every protected piece. Its ordinary
simultaneous certificate is recovered by forgetting the extra data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
inductive SynchronizedCentripetalChain (I : Type*) : {r s : ℕ} →
    (A : DefSet (rawMixedSpace (M := M) n r) S) →
    (B : DefSet (rawMixedSpace (M := M) n s) S) → Map A B →
    (I → DefSet (rawMixedSpace (M := M) n r) S) → Prop where
  | identity (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i, (P i).carrier ⊆ A.carrier)
      (hP : ∀ i, ProperInvariant S (P i).carrier) : SynchronizedCentripetalChain I A A (Map.id A) P
  | regularize (A : DefSet (rawMixedSpace (M := M) n r) S)
      (hA : ProperInvariant S A.carrier) (hVF : VFDoublyBounded A.carrier)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i, (P i).carrier ⊆ A.carrier)
      (hP : ∀ i, ProperInvariant S (P i).carrier) (hPVF : ∀ i, VFDoublyBounded (P i).carrier) :
      SynchronizedCentripetalChain I A (regularizeMap A).image (regularization A) P
  | centripetal (A : DefSet (rawMixedSpace (M := M) n r) S) (D : CentripetalData (G := G) A)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i, (P i).carrier ⊆ A.carrier)
      (E : ∀ i, CentripetalData (G := G) (P i))
      (hData : ∀ i,ApertureRestrictionData D (E i)) :
      SynchronizedCentripetalChain I A D.map.image D.bijection P
  | comp {A : DefSet (rawMixedSpace (M := M) n r) S}
      {B : DefSet (rawMixedSpace (M := M) n s) S}
      {C : DefSet (rawMixedSpace (M := M) n t) S} {f : Map A B} {g : Map B C}
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i, (P i).carrier ⊆ A.carrier)
      (hf : SynchronizedCentripetalChain I A B f P)
      (hg : SynchronizedCentripetalChain I B C g (fun i => (f.restrict (hPA i)).image)) :
      SynchronizedCentripetalChain I A C (g.comp f) P


theorem SynchronizedCentripetalChain.toSimultaneous {I : Type*} {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SynchronizedCentripetalChain (G := G) I A B f P) :
    SimultaneousCentripetalChain (G := G) I A B f P := by
  induction h with
  | identity A hA P hPA hP => exact .identity A hA P hPA hP
  | regularize A hA hVF P hPA hP hPVF => exact .regularize A hA hVF P hPA hP hPVF
  | centripetal A D P hPA E hData => exact .centripetal A D P hPA E (fun i p hp => (hData i).point p hp)
  | comp P hPA hf hg ihf ihg => exact .comp P hPA ihf ihg

theorem SynchronizedCentripetalChain.toChain {I : Type*} {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SynchronizedCentripetalChain (G := G) I A B f P) : CentripetalChain (G := G) A B f :=
  h.toSimultaneous.toChain

theorem SynchronizedCentripetalChain.atPiece {I : Type*} {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SynchronizedCentripetalChain (G := G) I A B f P) (i : I) :
    CompatibleCentripetalChain (G := G) A B f (P i) := h.toSimultaneous.atPiece i

end DiamondIntegral.Section6
