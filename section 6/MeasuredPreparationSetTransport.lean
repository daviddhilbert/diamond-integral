import «section 6».MeasuredPreparationTransport

/-! Actual measured preparations transport across equal source and
protected sets, with checked equality of the full actual source form. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem MeasuredCoordinatePreparation.transport_sets_form_compatible
    {A C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {P Q : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {hPA : ∀ i,(P i).carrier ⊆ A.carrier} {hQC : ∀ i,(Q i).carrier ⊆ C.carrier}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (F : MeasuredCoordinatePreparation (G := G) A P hPA ω)
    (hF : FormCompatibleSynchronizedChain (G := G) (Fin k) A F.target F.map P ω)
    (hAC : A=C) (hPQ : ∀ i,P i=Q i)
    (η : Map C (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hForm : ∀ p : A,(ω p).val=(η ⟨p.val,hAC ▸ p.property⟩).val) :
    ∃ T : MeasuredCoordinatePreparation (G := G) C Q hQC η,
      FormCompatibleSynchronizedChain (G := G) (Fin k) C T.target T.map Q η := by
  cases hAC
  let T : MeasuredCoordinatePreparation (G := G) A Q hQC η := (F.changeForm hForm).changePieces hPQ
  exact ⟨T,(hF.changeForm hForm).changePieces hPQ⟩

end DiamondIntegral.Section6
