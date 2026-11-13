import «section 3».GammaGroundGammaRepresentatives
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}


def gammaGroundGammaCoprodLeftCut (A B : GammaGroundGammaObject hc ground k) : Fin (A.tags + B.tags) → GammaGroundDefSet hc ground ((volumeGammaSpace hc).power (Fin k)) :=
  Fin.addCases A.piece (fun _ => GammaGroundDefSet.empty hc ground _)

theorem gammaGroundGammaCoprodLeftCut_subset (A B : GammaGroundGammaObject hc ground k) :
    ∀ i, (gammaGroundGammaCoprodLeftCut A B i).carrier ⊆ ((A.coprod B).piece i).carrier := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simpa only [gammaGroundGammaCoprodLeftCut, GammaGroundFiniteFamily.coprod, Fin.addCases_left] using Set.Subset.refl (A.piece a).carrier
  · simpa only [gammaGroundGammaCoprodLeftCut, GammaGroundFiniteFamily.coprod, Fin.addCases_right, GammaGroundDefSet.empty, GammaGroundDefSet.ofReal, DefSet.empty] using Set.empty_subset (B.piece b).carrier

def gammaGroundGammaCoprodLeftCutIso (A B : GammaGroundGammaObject hc ground k) :
    GammaGroundGammaObject.restrict (A.coprod B) (gammaGroundGammaCoprodLeftCut A B) ≅ A :=
  asIso (show _ ⟶ A from gammaGroundGammaCoprodEmptyRightHom A B.emptyPieces (fun _ => rfl))

def gammaGroundGammaCoprodRightCutIso (A B : GammaGroundGammaObject hc ground k) :
    GammaGroundGammaObject.restrict (A.coprod B) (GammaGroundGammaObject.difference (A.coprod B) (gammaGroundGammaCoprodLeftCut A B)) ≅ B := by
  let U : GammaGroundGammaObject hc ground k := A.coprod B
  let E : GammaGroundGammaObject hc ground k := A.emptyPieces.coprod B
  have hp : ∀ i, ((U.restrict (U.difference (gammaGroundGammaCoprodLeftCut A B))).piece i).carrier = (E.piece i).carrier := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp only [GammaGroundGammaObject.restrict, GammaGroundGammaObject.difference, gammaGroundGammaCoprodLeftCut, U, E, GammaGroundFiniteFamily.coprod,
        GammaGroundGammaObject.emptyPieces, Fin.addCases_left, GammaGroundDefSet.sdiff, GammaGroundDefSet.inter, GammaGroundDefSet.compl, GammaGroundDefSet.empty, GammaGroundDefSet.ofReal, DefSet.empty]
      exact Set.sdiff_self
    · simp only [GammaGroundGammaObject.restrict, GammaGroundGammaObject.difference, gammaGroundGammaCoprodLeftCut, U, E, GammaGroundFiniteFamily.coprod,
        GammaGroundGammaObject.emptyPieces, Fin.addCases_right, GammaGroundDefSet.sdiff, GammaGroundDefSet.inter, GammaGroundDefSet.compl, GammaGroundDefSet.empty, GammaGroundDefSet.ofReal, DefSet.empty]
      exact Set.sdiff_empty
  let e : U.restrict (U.difference (gammaGroundGammaCoprodLeftCut A B)) ≅ E :=
    asIso (show _ ⟶ _ from gammaGroundGammaTagHom _ _ (Equiv.refl _) hp)
  exact e.trans ((gammaGroundGammaCoprodCommIso A.emptyPieces B).trans
    (asIso (show B.coprod A.emptyPieces ⟶ B from gammaGroundGammaCoprodEmptyRightHom B A.emptyPieces (fun _ => rfl))))

end DiamondIntegral.Section3
