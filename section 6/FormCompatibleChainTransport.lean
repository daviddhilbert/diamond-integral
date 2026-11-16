import «section 6».FormCompatibleSynchronizedChains

/-! Literal source, target and protected-family transport for the
measured component invariant. Exact equality of the actual Gamma map
is retained when the source presentation changes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem FormCompatibleSynchronizedChain.changeTarget
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B C : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {g : Map A C}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (h : FormCompatibleSynchronizedChain (G := G) I A B f P ω) (hBC : B=C)
    (hMap : ∀ p : A,(f p).val=(g p).val) : FormCompatibleSynchronizedChain (G := G) I A C g P ω := by
  cases hBC
  have he : f=g := Map.ext (fun p => Subtype.ext (hMap p))
  rw [← he]
  exact h

theorem FormCompatibleSynchronizedChain.changePieces
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P Q : I → DefSet (rawMixedSpace (M := M) n r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (h : FormCompatibleSynchronizedChain (G := G) I A B f P ω) (he : ∀ i,P i=Q i) :
    FormCompatibleSynchronizedChain (G := G) I A B f Q ω := by
  rw [← funext he]
  exact h

theorem FormCompatibleSynchronizedChain.changeSource
    {A C : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {g : Map C B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    {η : Map C (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (h : FormCompatibleSynchronizedChain (G := G) I A B f P ω) (hAC : A=C)
    (hMap : ∀ p : A,(f p).val=(g ⟨p.val,hAC ▸ p.property⟩).val)
    (hForm : ∀ p : A,(ω p).val=(η ⟨p.val,hAC ▸ p.property⟩).val) :
    FormCompatibleSynchronizedChain (G := G) I C B g P η := by
  cases hAC
  have hf : f=g := Map.ext (fun p => Subtype.ext (hMap p))
  have hω : ω=η := Map.ext (fun p => Subtype.ext (hForm p))
  rw [← hf,← hω]
  exact h

end DiamondIntegral.Section6
