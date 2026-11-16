import «section 6».CoreFormCompatibility
import «section 6».SynchronizedFocusSteps

/-! The measured dimension-induction invariant retains the complete
common permitted chain and, at each centripetal component, constancy of
the current actual form on its contracted coordinate fibres. Intermediate
forms have exact transport; this is stronger than terminal constancy. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

inductive FormCompatibleSynchronizedChain (I : Type*) : {r s : ℕ} →
    (A : DefSet (rawMixedSpace (M := M) n r) S) →
    (B : DefSet (rawMixedSpace (M := M) n s) S) → Map A B →
    (I → DefSet (rawMixedSpace (M := M) n r) S) →
    Map A (DefSet.univ (rawGammaPresentation (M := M)) S) → Prop where
  | identity (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
      (hP : ∀ i,ProperInvariant S (P i).carrier)
      (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
      FormCompatibleSynchronizedChain I A A (Map.id A) P ω
  | regularize (A : DefSet (rawMixedSpace (M := M) n r) S)
      (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
      (hP : ∀ i,ProperInvariant S (P i).carrier) (hPD : ∀ i,VFDoublyBounded (P i).carrier)
      (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
      FormCompatibleSynchronizedChain I A (regularizeMap A).image (regularization A) P ω
  | centripetal (A : DefSet (rawMixedSpace (M := M) n r) S) (D : CentripetalData (G := G) A)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
      (E : ∀ i,CentripetalData (G := G) (P i)) (hData : ∀ i,ApertureRestrictionData D (E i))
      (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (hForm : D.CoreFormConstant ω) :
      FormCompatibleSynchronizedChain I A D.map.image D.bijection P ω
  | comp {A : DefSet (rawMixedSpace (M := M) n r) S}
      {B : DefSet (rawMixedSpace (M := M) n s) S} {C : DefSet (rawMixedSpace (M := M) n t) S}
      {f : Map A B} {g : Map B C}
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
      {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
      (hf : FormCompatibleSynchronizedChain I A B f P ω)
      (η : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
      (hTransport : ∀ p : A,(η (f p)).val=(ω p).val)
      (hg : FormCompatibleSynchronizedChain I B C g (fun i => (f.restrict (hPA i)).image) η) :
      FormCompatibleSynchronizedChain I A C (g.comp f) P ω

variable {r s : ℕ}

theorem FormCompatibleSynchronizedChain.toSynchronized {I : Type*}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (h : FormCompatibleSynchronizedChain (G := G) I A B f P ω) :
    SynchronizedCentripetalChain (G := G) I A B f P := by
  induction h with
  | identity A hA P hPA hP ω => exact .identity A hA P hPA hP
  | regularize A hA hAD P hPA hP hPD ω => exact .regularize A hA hAD P hPA hP hPD
  | centripetal A D P hPA E hData ω hForm => exact .centripetal A D P hPA E hData
  | comp P hPA hf η hTransport hg ihf ihg => exact .comp P hPA ihf ihg

end DiamondIntegral.Section6
