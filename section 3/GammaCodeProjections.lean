import «section 3».GammaProductDecomposition
import «section 3».RelationPullbacks

/-! Coordinate projections and concatenation identities on all full
Gamma codes are definable over the same original real base. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

def gammaCodeLeftMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k l : ℕ) :
    Map (DefSet.univ (codeSpace ((volumeGammaSpace hc).power (Fin (k + l)))) S)
      (DefSet.univ (codeSpace ((volumeGammaSpace hc).power (Fin k))) S) := by
  refine Map.ofCodes _ gammaCodeLeft (fun z p => z (Fin.castAdd l p.1, p.2))
    (fun _ => Set.DefinableFun.proj LRV) ?_ ?_
  · intro c i
    exact c.property (Fin.castAdd l i)
  · intro c
    exact Subtype.ext rfl

def gammaCodeRightMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k l : ℕ) :
    Map (DefSet.univ (codeSpace ((volumeGammaSpace hc).power (Fin (k + l)))) S)
      (DefSet.univ (codeSpace ((volumeGammaSpace hc).power (Fin l))) S) := by
  refine Map.ofCodes _ gammaCodeRight (fun z p => z (Fin.natAdd k p.1, p.2))
    (fun _ => Set.DefinableFun.proj LRV) ?_ ?_
  · intro c i
    exact c.property (Fin.natAdd k i)
  · intro c
    exact Subtype.ext rfl

theorem gammaCodeLeft_append
    (a : (codeSpace ((volumeGammaSpace hc).power (Fin k))).Carrier)
    (b : (codeSpace ((volumeGammaSpace hc).power (Fin l))).Carrier) :
    gammaCodeLeft (gammaCodeAppend a b) = a := by
  apply Subtype.ext
  funext p
  change Fin.append (fun i => a.val (i, p.2)) (fun j => b.val (j, p.2)) (Fin.castAdd l p.1) = a.val p
  exact Fin.append_left _ _ _

theorem gammaCodeRight_append
    (a : (codeSpace ((volumeGammaSpace hc).power (Fin k))).Carrier)
    (b : (codeSpace ((volumeGammaSpace hc).power (Fin l))).Carrier) :
    gammaCodeRight (gammaCodeAppend a b) = b := by
  apply Subtype.ext
  funext p
  change Fin.append (fun i => a.val (i, p.2)) (fun j => b.val (j, p.2)) (Fin.natAdd k p.1) = b.val p
  exact Fin.append_right _ _ _

theorem gammaCodeAppend_left_right
    (c : (codeSpace ((volumeGammaSpace hc).power (Fin (k + l)))).Carrier) :
    gammaCodeAppend (gammaCodeLeft c) (gammaCodeRight c) = c := by
  apply Subtype.ext
  funext p
  obtain ⟨i, j⟩ := p
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [gammaCodeAppend, gammaCodeLeft, gammaCodeRight, Fin.append_left]
  · simp only [gammaCodeAppend, gammaCodeLeft, gammaCodeRight, Fin.append_right]

theorem gammaProductCodePieceEquiv_left_val (A : GammaPiece hc S k) (B : GammaPiece hc S l)
    (c : codePreimage (gammaAppendMap A B).image) :
    (gammaProductCodePieceEquiv A B c).1.val = gammaCodeLeft c.val := by
  obtain ⟨a, b, rfl⟩ := gammaProductCode_surjective A B c
  rw [gammaProductCodePieceEquiv_code]
  exact (gammaCodeLeft_append a.val b.val).symm

theorem gammaProductCodePieceEquiv_right_val (A : GammaPiece hc S k) (B : GammaPiece hc S l)
    (c : codePreimage (gammaAppendMap A B).image) :
    (gammaProductCodePieceEquiv A B c).2.val = gammaCodeRight c.val := by
  obtain ⟨a, b, rfl⟩ := gammaProductCode_surjective A B c
  rw [gammaProductCodePieceEquiv_code]
  exact (gammaCodeRight_append a.val b.val).symm

end DiamondIntegral.Section3
