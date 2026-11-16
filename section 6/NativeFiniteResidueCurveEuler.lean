import «section 6».FiniteResidueCurveEuler

/-! The finite-point residue Euler conservation theorem applied to
the actual native residue field and an actual RV-definable full graph.
All isolation and hole conditions are explicit. The full special-chain
presentation theorem remains separate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem native_finite_residue_curve_euler_conservation
    (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    (A : DefSet (rawRVSpace (M := M) (2+2)) S)
    (P Q : Finset (ModelResidue M))
    (F E G D : Finset (Fin 2 → ModelResidue M))
    (hF : (F : Set (Fin 2 → ModelResidue M)) ⊆ TaggedLineMaps.space P)
    (hG : (G : Set (Fin 2 → ModelResidue M)) ⊆ TaggedLineMaps.space Q)
    (hE : Disjoint (TaggedLineMaps.space P) (E : Set (Fin 2 → ModelResidue M)))
    (hD : Disjoint (TaggedLineMaps.space Q) (D : Set (Fin 2 → ModelResidue M)))
    (f : (Fin 2 → ModelResidue M) → (Fin 2 → ModelResidue M))
    (hGraph : ∀ x y : Fin 2 → ModelResidue M,
      Fin.addCases (fun i => residueRV (x i)) (fun i => residueRV (y i)) ∈ A.carrier ↔
        x ∈ (TaggedLineMaps.space P \ F) ∪ E ∧ y = f x)
    (hBij : Set.BijOn f ((TaggedLineMaps.space P \ F) ∪ E) ((TaggedLineMaps.space Q \ G) ∪ D)) :
    (P.card : ℤ) - F.card + E.card = (Q.card : ℤ) - G.card + D.card := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  exact finite_curve_euler_conservation P Q F E G D hF hG hE hD f
    (IntegrationInACVF.Section3ACVF.ResidueFieldConservation.graph_definable hc A
      ((TaggedLineMaps.space P \ F) ∪ E) f hGraph) hBij

end DiamondIntegral.Section6
