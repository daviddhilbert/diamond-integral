import «section 3».GammaPartitions
import «section 3».FamilyEmptyCoproducts
import Section4.PositiveAdditiveRepresentatives

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

def gammaCoprodEmptyRightHom (A B : GammaObject hc S k) (hB : ∀ i, (B.piece i).carrier = ∅) :
    GammaHom (A.coprod B) A where
  bijection := familyCoprodEmptyRightBijection A B hB
  contraction := by
    have hBC : ∀ i, (B.codeLift.piece i).carrier = ∅ := by
      intro i
      ext c
      change (((volumeGammaSpace hc).power (Fin k)).decode c ∈ (B.piece i).carrier) ↔ False
      rw [hB i]
      exact Iff.rfl
    let F := (familyCoprodEmptyRightBijection A.codeLift B.codeLift hBC).comp (familyCodeCoprodBridge A B)
    refine ⟨F, fun c => ?_⟩
    rcases familyCodeCoprod_cases A B c with ⟨a, rfl⟩ | ⟨b, _⟩
    · change A.decode (familyCoprodDropEmpty A.codeLift B.codeLift hBC
        ((familyCodeCoprodBridge A B).equiv (familyCodeCoprodInl A B a))) =
        familyCoprodDropEmpty A B hB ((A.coprod B).decode (familyCodeCoprodInl A B a))
      rw [familyCodeCoprodBridge_inl, familyCoprodDropEmpty_inl,
        familyCodeCoprod_decode_inl, familyCoprodDropEmpty_inl]
    · exact False.elim (Set.notMem_empty b.2.val (hBC b.1 ▸ b.2.property))

def GammaObject.emptyPieces (A : GammaObject hc S k) : GammaObject hc S k :=
  ⟨A.tags, fun _ => DefSet.empty ((volumeGammaSpace hc).power (Fin k)) S⟩

theorem gammaClass_coprod (A B : GammaObject hc S k) :
    gammaClass (A.coprod B) = gammaClass A + gammaClass B := by
  let U : GammaObject hc S k := A.coprod B
  let X : Fin U.tags → DefSet ((volumeGammaSpace hc).power (Fin k)) S :=
    Fin.addCases A.piece (fun _ => DefSet.empty _ S)
  have hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [X, U, FiniteFamily.coprod, Fin.addCases_left] using (Set.Subset.refl (A.piece i).carrier)
    · simpa only [X, U, FiniteFamily.coprod, Fin.addCases_right, DefSet.empty] using (Set.empty_subset (B.piece j).carrier)
  have hA : gammaClass (U.restrict X) = gammaClass A :=
    gammaClass_iso (asIso (show U.restrict X ⟶ A from
      gammaCoprodEmptyRightHom A B.emptyPieces (fun _ => rfl)))
  let E : GammaObject hc S k := A.emptyPieces.coprod B
  have hp : ∀ i, ((U.restrict (U.difference X)).piece i).carrier = (E.piece i).carrier := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [GammaObject.restrict, GammaObject.difference, X, U, E, FiniteFamily.coprod,
        GammaObject.emptyPieces, Fin.addCases_left, DefSet.sdiff, DefSet.empty]
      exact Set.sdiff_self
    · simp only [GammaObject.restrict, GammaObject.difference, X, U, E, FiniteFamily.coprod,
        GammaObject.emptyPieces, Fin.addCases_right, DefSet.sdiff, DefSet.empty]
      exact Set.sdiff_empty
  let e : U.restrict (U.difference X) ≅ E :=
    asIso (show U.restrict (U.difference X) ⟶ E from gammaTagHom _ _ (Equiv.refl _) hp)
  have hB : gammaClass (U.restrict (U.difference X)) = gammaClass B :=
    gammaClass_iso (e.trans ((gammaCoprodCommIso A.emptyPieces B).trans
      (asIso (show B.coprod A.emptyPieces ⟶ B from gammaCoprodEmptyRightHom B A.emptyPieces (fun _ => rfl)))))
  have hs := gammaClass_scissor U X hX
  rw [hA, hB] at hs
  exact hs.symm

theorem gammaClass_surjective : Function.Surjective (gammaClass (M := M) (hc := hc) (S := S) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (gammaPresentation hc S k)
    FiniteFamily.coprod gammaClass_coprod

end DiamondIntegral.Section3
