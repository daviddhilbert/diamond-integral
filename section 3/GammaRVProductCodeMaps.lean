import «section 3».GammaRVProductLift
import «section 3».MeasuredGammaRVLift

/-! Product lift maps on every full Gamma code. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

theorem gammaCodeAppend_tuple
    (a : (codeSpace ((volumeGammaSpace hc).power (Fin k))).Carrier)
    (b : (codeSpace ((volumeGammaSpace hc).power (Fin l))).Carrier) :
    gammaCodeTuple (gammaCodeAppend a b) = rvAppend (gammaCodeTuple a) (gammaCodeTuple b) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [rvAppend, Fin.append_left]
    apply Subtype.ext
    change Fin.append (fun i => a.val (i, (0 : Fin 1))) (fun j => b.val (j, (0 : Fin 1))) (Fin.castAdd l i) = _
    exact Fin.append_left _ _ _
  · simp only [rvAppend, Fin.append_right]
    apply Subtype.ext
    change Fin.append (fun i => a.val (i, (0 : Fin 1))) (fun j => b.val (j, (0 : Fin 1))) (Fin.natAdd k j) = _
    exact Fin.append_right _ _ _

def gammaProductCode (A : GammaPiece hc S k) (B : GammaPiece hc S l)
    (a : codePreimage A) (b : codePreimage B) : codePreimage (gammaAppendMap A B).image :=
  ⟨gammaCodeAppend a.val b.val, ⟨⟨((((volumeGammaSpace hc).power (Fin k)).decode a.val),
    (((volumeGammaSpace hc).power (Fin l)).decode b.val)), a.property, b.property⟩,
      (gammaCodeAppend_decode a.val b.val).symm⟩⟩

theorem gammaProductCode_surjective (A : GammaPiece hc S k) (B : GammaPiece hc S l)
    (c : codePreimage (gammaAppendMap A B).image) :
    ∃ a b, gammaProductCode A B a b = c := by
  have ht := (gammaRVCodeLift_product A B).le
    (show gammaCodeTuple c.val ∈ (gammaRVCodeLift (gammaAppendMap A B).image).domain.carrier from ⟨c, rfl⟩)
  obtain ⟨p, hp⟩ := ht
  obtain ⟨a, ha⟩ := p.property.1
  obtain ⟨b, hb⟩ := p.property.2
  refine ⟨a, b, Subtype.ext ?_⟩
  apply gammaCodeTuple_injective
  change gammaCodeTuple (gammaCodeAppend a.val b.val) = _
  rw [gammaCodeAppend_tuple]
  exact (congrArg₂ rvAppend ha hb).trans hp

theorem gammaRVProductBijection_code (A : GammaObject hc S k) (B : GammaObject hc S l)
    (i : Fin (A.tags * B.tags))
    (a : codePreimage (A.piece (finProdFinEquiv.symm i).1))
    (b : codePreimage (B.piece (finProdFinEquiv.symm i).2)) :
    (gammaRVProductBijection A B).map ((A.product B).rvEncodeCode
      ⟨i, gammaProductCode _ _ a b⟩) =
      rvPackPair A.rvLift.domain B.rvLift.domain
        (A.rvEncodeCode ⟨(finProdFinEquiv.symm i).1, a⟩)
        (B.rvEncodeCode ⟨(finProdFinEquiv.symm i).2, b⟩) := by
  change rvFamilyProductMap A.rvPieces B.rvPieces
    (rvFamilyMap (gammaRVProductFamilies A B).equiv (gammaRVProductFamilies A B).definable
      ((A.product B).rvPieces.rvEncode _)) = _
  rw [rvFamilyMap_encode]
  have he : (gammaRVProductFamilies A B).equiv
      ((A.product B).rvCodeBijection.equiv ⟨i, gammaProductCode _ _ a b⟩) =
      (⟨i, rvPackPair _ _ ((gammaRVCodeBijection _).map a)
        ((gammaRVCodeBijection _).map b)⟩ : (A.rvPieces.rvProduct B.rvPieces).Carrier) := by
    apply congrArg (fun p : (A.rvPieces.rvProduct B.rvPieces).piece i =>
      (⟨i, p⟩ : (A.rvPieces.rvProduct B.rvPieces).Carrier))
    apply Subtype.ext
    exact gammaCodeAppend_tuple a.val b.val
  rw [he]
  change rvFamilyDesc (A.rvPieces.rvProduct B.rvPieces) _ _ _ = _
  rw [rvFamilyDesc_encode, rvFamilyProductBranch_pair]
  rfl

end DiamondIntegral.Section3
