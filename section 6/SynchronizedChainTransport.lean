import «section 6».SynchronizedCentripetalChains

/-! Literal target and partition transport for synchronized finite
centripetal chains. These certificates retain the actual common
component sequence needed by the preparation dimension induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem SynchronizedCentripetalChain.changeTarget
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B C : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {g : Map A C}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SynchronizedCentripetalChain (G := G) I A B f P) (hBC : B=C)
    (hMap : ∀ p : A,(f p).val=(g p).val) : SynchronizedCentripetalChain (G := G) I A C g P := by
  cases hBC
  have he : f=g := Map.ext (fun p => Subtype.ext (hMap p))
  rw [← he]
  exact h

theorem SynchronizedCentripetalChain.changePieces
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P Q : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SynchronizedCentripetalChain (G := G) I A B f P) (he : ∀ i,P i=Q i) :
    SynchronizedCentripetalChain (G := G) I A B f Q := by
  have hPQ := funext he
  rw [← hPQ]
  exact h

theorem SynchronizedCentripetalChain.changeSource
    {A C : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {g : Map C B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SynchronizedCentripetalChain (G := G) I A B f P) (hAC : A=C)
    (hMap : ∀ p : A,(f p).val=(g ⟨p.val,hAC ▸ p.property⟩).val) :
    SynchronizedCentripetalChain (G := G) I C B g P := by
  cases hAC
  have he : f=g := Map.ext (fun p => Subtype.ext (hMap p))
  rw [← he]
  exact h

end DiamondIntegral.Section6
