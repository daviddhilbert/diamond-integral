import «section 6».TransportedProtectedFamilies
import «section 6».RVRefinementProperDescent
import «section 6».RVRefinementSynchronizedChains

/-! Actual proper joint partition pieces and their preparation lift.
The covered joint problem retains the precise unfinished global fusion
problem; its original-base geometry and transport back are constructed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k l : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def PreparedSynchronizedFamily.changePieces
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {P Q : I → DefSet (rawMixedSpace (M := M) n r) S}
    {hPA : ∀ i,(P i).carrier ⊆ A.carrier} {hQA : ∀ i,(Q i).carrier ⊆ A.carrier}
    (F : PreparedSynchronizedFamily (G := G) A P hPA) (he : ∀ i,P i=Q i) :
    PreparedSynchronizedFamily (G := G) A Q hQA := by
  have hPQ := funext he
  cases hPQ
  exact F

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+1))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S}
namespace FrozenCoordinateProgramData

theorem covered_joint_piece_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P)
    (hPX : ∀ i,(P i).carrier ⊆ X.source.carrier) (i : Fin l) :
    ProperInvariant S ((F.actualAmbientRefinement h00 U).coveredPiece
      (unaryIndexedMixedFamily (F.oldParameterMap h00) (headFibreTemplate (P i)))).carrier := by
  apply (F.actualAmbientRefinement h00 U).coveredPiece_properInvariant h00 hc hκ hs hv U.target.pullback
  rw [F.actual_refinement_piece_eq h00 U hPX i]
  exact U.image_proper h00 hc linear hκ hs hv hsmall hΓ hPX i

theorem covered_joint_preparation_lifts
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P)
    (hPX : ∀ i,(P i).carrier ⊆ X.source.carrier)
    (H : PreparedSynchronizedFamily (G := G) (F.actualAmbientRefinement h00 U).coveredBase
      (fun i => (F.actualAmbientRefinement h00 U).coveredPiece
        (unaryIndexedMixedFamily (F.oldParameterMap h00) (headFibreTemplate (P i))))
      (fun _ _ hp => hp.2)) :
    Nonempty (PreparedSynchronizedFamily (G := G) U.target.source
      (fun i => (U.map.restrict (hPX i)).image) (U.image_subset hPX)) := by
  let Z := F.actualAmbientRefinement h00 U
  obtain ⟨K⟩ := H.refine_rv_labels h00 hc hκ hs hv Z.coveredFrame
  exact ⟨K.changePieces (fun i =>
    (Z.selected_coveredPiece_eq _).trans (F.actual_refinement_piece_eq h00 U hPX i))⟩

end FrozenCoordinateProgramData
end DiamondIntegral.Section6
