import Section4.PositiveAdditiveRepresentatives
import «section 3».GammaGroundGammaPartitions
import «section 3».GammaGroundFamilyEmptyCoproducts
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

def gammaGroundGammaCoprodEmptyRightHom (A B : GammaGroundGammaObject hc ground k) (hB : ∀ i, (B.piece i).carrier = ∅) :
    GammaGroundGammaHom (A.coprod B) A where
  bijection := gammaGroundFamilyCoprodEmptyRightBijection A B hB
  contraction := by
    have hBC : ∀ i, (B.codeLift.piece i).carrier = ∅ := by
      intro i
      ext c
      change (((volumeGammaSpace hc).power (Fin k)).decode c ∈ (B.piece i).carrier) ↔ False
      rw [hB i]
      exact Iff.rfl
    let F := (gammaGroundFamilyCoprodEmptyRightBijection A.codeLift B.codeLift hBC).comp (gammaGroundFamilyCodeCoprodBridge A B)
    refine ⟨F, fun c => ?_⟩
    rcases gammaGroundFamilyCodeCoprod_cases A B c with ⟨a, rfl⟩ | ⟨b, _⟩
    · change A.decode (gammaGroundFamilyCoprodDropEmpty A.codeLift B.codeLift hBC
        ((gammaGroundFamilyCodeCoprodBridge A B).equiv (gammaGroundFamilyCodeCoprodInl A B a))) =
        gammaGroundFamilyCoprodDropEmpty A B hB ((A.coprod B).decode (gammaGroundFamilyCodeCoprodInl A B a))
      rw [gammaGroundFamilyCodeCoprodBridge_inl, gammaGroundFamilyCoprodDropEmpty_inl,
        gammaGroundFamilyCodeCoprod_decode_inl, gammaGroundFamilyCoprodDropEmpty_inl]
    · exact False.elim (Set.notMem_empty b.2.val (hBC b.1 ▸ b.2.property))

def GammaGroundGammaObject.emptyPieces (A : GammaGroundGammaObject hc ground k) : GammaGroundGammaObject hc ground k :=
  ⟨A.tags, fun _ => GammaGroundDefSet.empty hc ground ((volumeGammaSpace hc).power (Fin k))⟩

theorem gammaGroundGammaClass_coprod (A B : GammaGroundGammaObject hc ground k) :
    gammaGroundGammaClass (A.coprod B) = gammaGroundGammaClass A + gammaGroundGammaClass B := by
  let U : GammaGroundGammaObject hc ground k := A.coprod B
  let X : Fin U.tags → GammaGroundDefSet hc ground ((volumeGammaSpace hc).power (Fin k)) :=
    Fin.addCases A.piece (fun _ => GammaGroundDefSet.empty hc ground _)
  have hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [X, U, GammaGroundFiniteFamily.coprod, Fin.addCases_left] using (Set.Subset.refl (A.piece i).carrier)
    · simpa only [X, U, GammaGroundFiniteFamily.coprod, Fin.addCases_right, GammaGroundDefSet.empty, GammaGroundDefSet.ofReal, DefSet.empty] using (Set.empty_subset (B.piece j).carrier)
  have hA : gammaGroundGammaClass (U.restrict X) = gammaGroundGammaClass A :=
    gammaGroundGammaClass_iso (asIso (show U.restrict X ⟶ A from
      gammaGroundGammaCoprodEmptyRightHom A B.emptyPieces (fun _ => rfl)))
  let E : GammaGroundGammaObject hc ground k := A.emptyPieces.coprod B
  have hp : ∀ i, ((U.restrict (U.difference X)).piece i).carrier = (E.piece i).carrier := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [GammaGroundGammaObject.restrict, GammaGroundGammaObject.difference, X, U, E, GammaGroundFiniteFamily.coprod,
        GammaGroundGammaObject.emptyPieces, Fin.addCases_left, GammaGroundDefSet.sdiff, GammaGroundDefSet.inter, GammaGroundDefSet.compl, GammaGroundDefSet.empty, GammaGroundDefSet.ofReal, DefSet.empty]
      exact Set.sdiff_self
    · simp only [GammaGroundGammaObject.restrict, GammaGroundGammaObject.difference, X, U, E, GammaGroundFiniteFamily.coprod,
        GammaGroundGammaObject.emptyPieces, Fin.addCases_right, GammaGroundDefSet.sdiff, GammaGroundDefSet.inter, GammaGroundDefSet.compl, GammaGroundDefSet.empty, GammaGroundDefSet.ofReal, DefSet.empty]
      exact Set.sdiff_empty
  let e : U.restrict (U.difference X) ≅ E :=
    asIso (show U.restrict (U.difference X) ⟶ E from gammaGroundGammaTagHom _ _ (Equiv.refl _) hp)
  have hB : gammaGroundGammaClass (U.restrict (U.difference X)) = gammaGroundGammaClass B :=
    gammaGroundGammaClass_iso (e.trans ((gammaGroundGammaCoprodCommIso A.emptyPieces B).trans
      (asIso (show B.coprod A.emptyPieces ⟶ B from gammaGroundGammaCoprodEmptyRightHom B A.emptyPieces (fun _ => rfl)))))
  have hs := gammaGroundGammaClass_scissor U X hX
  rw [hA, hB] at hs
  exact hs.symm

theorem gammaGroundGammaClass_surjective : Function.Surjective (gammaGroundGammaClass (M := M) (hc := hc) (ground := ground) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (gammaGroundGammaPresentation hc ground k)
    GammaGroundFiniteFamily.coprod gammaGroundGammaClass_coprod

end DiamondIntegral.Section3
