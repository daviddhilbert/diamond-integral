import «section 3».GammaRVCodeLift
import «section 3».FamilyPieceMaps
import «section 3».GammaScissors
import Section4.ProductBijections

/-! Actual Gamma products concatenate coordinates and retain finite
family tags. Finite Gamma domains remain finite under these products. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

def gammaAppendMap (A : GammaPiece hc S k) (B : GammaPiece hc S l) :
    Map (A.prod B) (DefSet.univ ((volumeGammaSpace hc).power (Fin (k + l))) S) := by
  let F (z : (Fin k × Fin 1) ⊕ (Fin l × Fin 1) → M) (ij : Fin (k + l) × Fin 1) : M :=
    Fin.append (fun i => z (.inl (i, ij.2))) (fun j => z (.inr (j, ij.2))) ij.1
  refine Map.ofCodes (A.prod B)
    (fun p : (Fin k → Values.Gamma (M := M)) × (Fin l → Values.Gamma (M := M)) => Fin.append p.1 p.2)
    F ?_ ?_ ?_
  · change S.DefinableMap LRV F
    rintro ⟨i, j0⟩
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [F, Fin.append_left] using
        (show S.DefinableFun LRV (fun z : (Fin k × Fin 1) ⊕ (Fin l × Fin 1) → M => z (.inl (i, j0))) from Set.DefinableFun.proj LRV)
    · simpa only [F, Fin.append_right] using
        (show S.DefinableFun LRV (fun z : (Fin k × Fin 1) ⊕ (Fin l × Fin 1) → M => z (.inr (j, j0))) from Set.DefinableFun.proj LRV)
  · intro c i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [F, Fin.append_left, Function.comp_def] using c.property.1 i
    · simpa only [F, Fin.append_right, Function.comp_def] using c.property.2 j
  · intro c
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      apply Subtype.ext
      apply congrArg Values.vrv
      apply Subtype.ext
      change F c.val (Fin.castAdd l i, (0 : Fin 1)) = c.val (.inl (i, (0 : Fin 1)))
      simp only [F, Fin.append_left]
    · simp only [Fin.append_right]
      apply Subtype.ext
      apply congrArg Values.vrv
      apply Subtype.ext
      change F c.val (Fin.natAdd k j, (0 : Fin 1)) = c.val (.inr (j, (0 : Fin 1)))
      simp only [F, Fin.append_right]

theorem gammaAppendMap_injective (A : GammaPiece hc S k) (B : GammaPiece hc S l) :
    Function.Injective (gammaAppendMap A B) := by
  intro a b he
  apply Subtype.ext
  apply Prod.ext
  · funext i
    simpa only [gammaAppendMap, Map.ofCodes, Fin.append_left] using
      congrArg (fun t : DefSet.univ ((volumeGammaSpace hc).power (Fin (k + l))) S =>
        t.val (Fin.castAdd l i)) he
  · funext j
    simpa only [gammaAppendMap, Map.ofCodes, Fin.append_right] using
      congrArg (fun t : DefSet.univ ((volumeGammaSpace hc).power (Fin (k + l))) S =>
        t.val (Fin.natAdd k j)) he

def gammaAppendBijection (A : GammaPiece hc S k) (B : GammaPiece hc S l) :
    DefinableBijection (A.prod B) (gammaAppendMap A B).image :=
  ⟨(gammaAppendMap A B).toImage, by
    constructor
    · intro a b he
      apply gammaAppendMap_injective A B
      exact Subtype.ext (congrArg (fun x : (gammaAppendMap A B).image => x.val) he)
    · intro b
      obtain ⟨a, ha⟩ := b.property
      exact ⟨a, Subtype.ext ha⟩⟩

def GammaObject.product (A : GammaObject hc S k) (B : GammaObject hc S l) : GammaObject hc S (k + l) :=
  ⟨A.tags * B.tags, fun i => (gammaAppendMap
    (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)).image⟩

def GammaObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) : GammaObject hc S 0 :=
  ⟨1, fun _ => DefSet.univ ((volumeGammaSpace hc).power (Fin 0)) S⟩

theorem GammaObject.degree_zero_finite (A : GammaObject hc S 0) : finiteGammaProperty A := by
  intro i
  exact Set.Subsingleton.finite (fun x _ y _ => funext (fun j => j.elim0))

theorem GammaObject.product_finite (A : GammaObject hc S k) (B : GammaObject hc S l)
    (hA : finiteGammaProperty A) (hB : finiteGammaProperty B) : finiteGammaProperty (A.product B) := by
  intro i
  apply (((hA (finProdFinEquiv.symm i).1).prod (hB (finProdFinEquiv.symm i).2)).image
    (fun p : (Fin k → Values.Gamma (M := M)) × (Fin l → Values.Gamma (M := M)) => Fin.append p.1 p.2)).subset
  rintro t ⟨a, ha⟩
  exact ⟨a.val, a.property, ha⟩

def FiniteGammaObject.product (A : FiniteGammaObject hc S k) (B : FiniteGammaObject hc S l) :
    FiniteGammaObject hc S (k + l) := ⟨A.obj.product B.obj, A.obj.product_finite B.obj A.property B.property⟩

def FiniteGammaObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    FiniteGammaObject hc S 0 := ⟨GammaObject.unit hc S, (GammaObject.unit hc S).degree_zero_finite⟩

end DiamondIntegral.Section3
