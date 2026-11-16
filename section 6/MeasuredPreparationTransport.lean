import «section 6».MeasuredFormCompatibleTargets

/-! Literal protected-family and source-form changes for actual measured
preparations. The underlying maps and all prepared images are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {P Q : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {hPA : ∀ i,(P i).carrier ⊆ A.carrier} {hQA : ∀ i,(Q i).carrier ⊆ A.carrier}
variable {ω η : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}

def MeasuredCoordinatePreparation.toPreparedSynchronized
    (F : MeasuredCoordinatePreparation (G := G) A P hPA ω)
    (h : SynchronizedCentripetalChain (G := G) (Fin k) A F.target F.map P) :
    PreparedSynchronizedFamily (G := G) A P hPA :=
  ⟨F.arity,F.target,F.map,h,F.proper,F.doublyBounded,F.prepared,fun i => (F.pieces i).2⟩

def MeasuredCoordinatePreparation.changePieces
    (F : MeasuredCoordinatePreparation (G := G) A P hPA ω) (he : ∀ i,P i=Q i) :
    MeasuredCoordinatePreparation (G := G) A Q hQA ω := {
  arity := F.arity
  target := F.target
  map := F.map
  special := F.special
  proper := F.proper
  doublyBounded := F.doublyBounded
  prepared := F.prepared
  tagged := F.tagged
  form := F.form
  transport := F.transport
  constant := F.constant
  pieces := by
    intro i
    have h := funext he
    cases h
    exact F.pieces i }

def MeasuredCoordinatePreparation.changeForm
    (F : MeasuredCoordinatePreparation (G := G) A P hPA ω)
    (he : ∀ p : A,(ω p).val=(η p).val) : MeasuredCoordinatePreparation (G := G) A P hPA η := {
  arity := F.arity
  target := F.target
  map := F.map
  special := F.special
  proper := F.proper
  doublyBounded := F.doublyBounded
  prepared := F.prepared
  tagged := F.tagged
  form := F.form
  transport := fun p => (F.transport p).trans (he p)
  constant := F.constant
  pieces := F.pieces }

theorem FormCompatibleSynchronizedChain.changeForm {s : ℕ}
    {B : DefSet (rawMixedSpace (M := M) (n+1) s) S} {f : Map A B}
    (h : FormCompatibleSynchronizedChain (G := G) (Fin k) A B f P ω)
    (he : ∀ p : A,(ω p).val=(η p).val) :
    FormCompatibleSynchronizedChain (G := G) (Fin k) A B f P η :=
  h.changeSource rfl (fun _ => rfl) he

end DiamondIntegral.Section6
