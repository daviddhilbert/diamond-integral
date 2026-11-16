import «section 6».FrozenMeasuredCoordinateProgramData

/-! The actual measured frozen family retains all existing geometric
program data, with exactly the same unary map and ambient lift. Freezing
also leaves the actual full Gamma form unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+2))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+2) X.arity) S}
variable {ω : Map X.source (DefSet.univ (rawGammaPresentation (M := M)) S)}
namespace FrozenMeasuredCoordinateProgramData

def forget (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω) :
    FrozenCoordinateProgramData (G := G) A C hCA X P := {
  programs := F.programs.forget
  unary := {
    freezing := F.unary.freezing
    arity := F.unary.arity
    target := F.unary.target
    map := F.unary.map
    chain := F.unary.chain
    proper := F.unary.proper
    doublyBounded := F.unary.doublyBounded
    pullback := F.unary.pullback
    tagged := F.unary.tagged
    pieces := F.unary.pieces
    lift := ⟨F.unary.lift⟩
    ambientProduct := F.unary.ambientProduct
    protectedProducts := F.unary.protectedProducts
    unaryProducts := F.unary.unaryProducts
    data := fun p q he => geometric_data_eq_of_measured_data_eq h00 F.programs.programs
      (headFibreTemplate X.source) (fun i => headFibreTemplate (P i)) (headGammaFormTemplate ω)
      F.programs.choices F.programs.choices_definable _ _ (F.unary.data p q he) } }

theorem frozen_gamma_equal
    (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω) :
    FMT.frozenGammaForm F.unary.freezing.balls F.unary.freezing.centers (0 : Fin (n+2))
      F.unary.freezing.separated F.unary.freezing.balls_definable F.unary.freezing.centers_definable
      F.unary.ambientProduct ω=ω :=
  FMT.frozenGammaForm_eq _ _ _ _ _ _ _ ω F.unary.formProducts

end FrozenMeasuredCoordinateProgramData
end DiamondIntegral.Section6
