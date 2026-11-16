import «section 6».RVRefinementCoveredBases

/-! Full coordinate stability transfers to actual label refinements.
An inhabited new fibre is the whole corresponding old fibre, so a
replacement keeps every extra label and every protected membership. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.RVRefinementFrame
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem coordinate_replacement_mem (X : RVRefinementFrame A) (p : X.base) (j : Fin n) (x : VF M)
    (hOld : (Function.update p.val.1 j x,p.val.2 ∘ X.labels) ∈ A.carrier) :
    (Function.update p.val.1 j x,p.val.2) ∈ X.base.carrier := by
  change Function.update p.val.1 j x ∈ vfFibre X.base.carrier p.val.2
  rw [X.fibre_eq_of_mem p]
  exact hOld

theorem selectedPiece_coordinate_stable
    (X : RVRefinementFrame A) (Q : DefSet (rawMixedSpace (M := M) n r) S)
    (hQA : Q.carrier ⊆ A.carrier) (U : Set (Fin r → RVInfinity M))
    (j : Fin n) (ρ : (Fin r → RVInfinity M) → Gamma M)
    (hStable : ∀ p ∈ Q.carrier,p.2 ∈ U → ∀ x : VF M,
      (ρ p.2).val < vfValue (p.1 j-x) → (Function.update p.1 j x,p.2) ∈ Q.carrier) :
    ∀ p ∈ (X.selectedPiece Q).carrier,p.2 ∘ X.labels ∈ U → ∀ x : VF M,
      (ρ (p.2 ∘ X.labels)).val < vfValue (p.1 j-x) →
        (Function.update p.1 j x,p.2) ∈ (X.selectedPiece Q).carrier := by
  intro p hp hu x hx
  obtain ⟨hpC,hpQ⟩ := (X.mem_selectedPiece Q p).mp hp
  have hNew := hStable (p.1,p.2 ∘ X.labels) hpQ hu x hx
  exact (X.mem_selectedPiece Q _).mpr
    ⟨X.coordinate_replacement_mem ⟨p,hpC⟩ j x (hQA hNew),hNew⟩

end DiamondIntegral.Section6.RVRefinementFrame
