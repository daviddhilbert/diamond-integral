import «section 3».GammaRepresentatives

/-! Every fixed-degree positive Gamma class is represented by an actual
tagged Gamma object. Addition is the genuine disjoint union. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}


def gammaCoprodLeftCut (A B : GammaObject hc S k) : Fin (A.tags + B.tags) → DefSet ((volumeGammaSpace hc).power (Fin k)) S :=
  Fin.addCases A.piece (fun _ => DefSet.empty _ S)

theorem gammaCoprodLeftCut_subset (A B : GammaObject hc S k) :
    ∀ i, (gammaCoprodLeftCut A B i).carrier ⊆ ((A.coprod B).piece i).carrier := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simpa only [gammaCoprodLeftCut, FiniteFamily.coprod, Fin.addCases_left] using Set.Subset.refl (A.piece a).carrier
  · simpa only [gammaCoprodLeftCut, FiniteFamily.coprod, Fin.addCases_right, DefSet.empty] using Set.empty_subset (B.piece b).carrier

def gammaCoprodLeftCutIso (A B : GammaObject hc S k) :
    GammaObject.restrict (A.coprod B) (gammaCoprodLeftCut A B) ≅ A :=
  asIso (show _ ⟶ A from gammaCoprodEmptyRightHom A B.emptyPieces (fun _ => rfl))

def gammaCoprodRightCutIso (A B : GammaObject hc S k) :
    GammaObject.restrict (A.coprod B) (GammaObject.difference (A.coprod B) (gammaCoprodLeftCut A B)) ≅ B := by
  let U : GammaObject hc S k := A.coprod B
  let E : GammaObject hc S k := A.emptyPieces.coprod B
  have hp : ∀ i, ((U.restrict (U.difference (gammaCoprodLeftCut A B))).piece i).carrier = (E.piece i).carrier := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp only [GammaObject.restrict, GammaObject.difference, gammaCoprodLeftCut, U, E, FiniteFamily.coprod,
        GammaObject.emptyPieces, Fin.addCases_left, DefSet.sdiff, DefSet.empty]
      exact Set.sdiff_self
    · simp only [GammaObject.restrict, GammaObject.difference, gammaCoprodLeftCut, U, E, FiniteFamily.coprod,
        GammaObject.emptyPieces, Fin.addCases_right, DefSet.sdiff, DefSet.empty]
      exact Set.sdiff_empty
  let e : U.restrict (U.difference (gammaCoprodLeftCut A B)) ≅ E :=
    asIso (show _ ⟶ _ from gammaTagHom _ _ (Equiv.refl _) hp)
  exact e.trans ((gammaCoprodCommIso A.emptyPieces B).trans
    (asIso (show B.coprod A.emptyPieces ⟶ B from gammaCoprodEmptyRightHom B A.emptyPieces (fun _ => rfl))))

end DiamondIntegral.Section3
