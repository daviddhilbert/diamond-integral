import IntegrationSection3.TaggedCofiniteConservation
import IntegrationSection3ACVF.ResidueFieldConservation

/-! An actual RV-definable graph between cofinite finite unions of
native residue affine lines preserves their finite Euler count. The
canonical ACVF-to-residue definability bridge and algebraic closedness
are constructed from the pinned earlier results. No Euler or HK input
is assumed. This is a conservation theorem for the displayed residue
presentations, not yet a trace extraction theorem for all special chains. -/

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

theorem native_residue_curve_components_and_holes
    (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    (A : DefSet (rawRVSpace (M := M) (2+2)) S)
    (P Q : Finset (ModelResidue M))
    (F G : Finset (Fin 2 → ModelResidue M))
    (hF : (F : Set (Fin 2 → ModelResidue M)) ⊆ TaggedLineMaps.space P)
    (hG : (G : Set (Fin 2 → ModelResidue M)) ⊆ TaggedLineMaps.space Q)
    (f : (Fin 2 → ModelResidue M) → (Fin 2 → ModelResidue M))
    (hGraph : ∀ x y : Fin 2 → ModelResidue M,
      Fin.addCases (fun i => residueRV (x i)) (fun i => residueRV (y i)) ∈ A.carrier ↔
        x ∈ TaggedLineMaps.space P \ F ∧ y = f x)
    (hBij : Set.BijOn f (TaggedLineMaps.space P \ F) (TaggedLineMaps.space Q \ G)) :
    P.card = Q.card ∧ F.card = G.card := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  exact TaggedCofiniteConservation.components_and_holes Set.univ P Q F G hF hG f
    (IntegrationInACVF.Section3ACVF.ResidueFieldConservation.graph_definable hc A
      (TaggedLineMaps.space P \ F) f hGraph) hBij

theorem native_residue_curve_euler_conservation
    (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    (A : DefSet (rawRVSpace (M := M) (2+2)) S)
    (P Q : Finset (ModelResidue M))
    (F G : Finset (Fin 2 → ModelResidue M))
    (hF : (F : Set (Fin 2 → ModelResidue M)) ⊆ TaggedLineMaps.space P)
    (hG : (G : Set (Fin 2 → ModelResidue M)) ⊆ TaggedLineMaps.space Q)
    (f : (Fin 2 → ModelResidue M) → (Fin 2 → ModelResidue M))
    (hGraph : ∀ x y : Fin 2 → ModelResidue M,
      Fin.addCases (fun i => residueRV (x i)) (fun i => residueRV (y i)) ∈ A.carrier ↔
        x ∈ TaggedLineMaps.space P \ F ∧ y = f x)
    (hBij : Set.BijOn f (TaggedLineMaps.space P \ F) (TaggedLineMaps.space Q \ G)) :
    (P.card : ℤ) - F.card = (Q.card : ℤ) - G.card := by
  obtain ⟨hComponents,hHoles⟩ := native_residue_curve_components_and_holes hc A P Q F G hF hG f hGraph hBij
  rw [hComponents,hHoles]

end DiamondIntegral.Section6
