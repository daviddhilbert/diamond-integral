import «section 3».GammaGroundGammaRVCodeLift
import «section 3».GammaGroundGammaScissors
import «section 3».GammaGroundFiniteGammaScissors
import «section 3».GammaProducts

/-! Actual Gamma-ground family products concatenate coordinates and
retain their tags; finite pieces stay finite. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def gammaGroundGammaAppendMap (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l) :
    GammaGroundMap (A.prod B) (GammaGroundDefSet.univ hc ground ((volumeGammaSpace hc).power (Fin (k + l)))) :=
  GammaGroundMap.ofGlobal _ _ ((gammaAppendMap
    (DefSet.univ ((volumeGammaSpace hc).power (Fin k)) ground.real)
    (DefSet.univ ((volumeGammaSpace hc).power (Fin l)) ground.real)).comp
      ((universalProductFst ((volumeGammaSpace hc).power (Fin k)) ((volumeGammaSpace hc).power (Fin l)) ground.real).pair
        (universalProductSnd ((volumeGammaSpace hc).power (Fin k)) ((volumeGammaSpace hc).power (Fin l)) ground.real)))
    (fun _ => Set.mem_univ _)

theorem gammaGroundGammaAppendMap_injective (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l) :
    Function.Injective (gammaGroundGammaAppendMap A B) := by
  intro a b he
  apply Subtype.ext
  apply Prod.ext
  · funext i
    have hi := congrArg (fun t : GammaGroundDefSet.univ hc ground ((volumeGammaSpace hc).power (Fin (k + l))) =>
      t.val (Fin.castAdd l i)) he
    change Fin.append a.val.1 a.val.2 (Fin.castAdd l i) = Fin.append b.val.1 b.val.2 (Fin.castAdd l i) at hi
    simpa only [Fin.append_left] using hi
  · funext j
    have hj := congrArg (fun t : GammaGroundDefSet.univ hc ground ((volumeGammaSpace hc).power (Fin (k + l))) =>
      t.val (Fin.natAdd k j)) he
    change Fin.append a.val.1 a.val.2 (Fin.natAdd k j) = Fin.append b.val.1 b.val.2 (Fin.natAdd k j) at hj
    simpa only [Fin.append_right] using hj

def gammaGroundGammaAppendBijection (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l) :
    GammaGroundBijection (A.prod B) (gammaGroundGammaAppendMap A B).image :=
  ⟨(gammaGroundGammaAppendMap A B).toImage,
    (gammaGroundGammaAppendMap A B).toImage_bijective (gammaGroundGammaAppendMap_injective A B)⟩

def GammaGroundGammaObject.product (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l) :
    GammaGroundGammaObject hc ground (k + l) :=
  ⟨A.tags * B.tags, fun i => (gammaGroundGammaAppendMap
    (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)).image⟩

def GammaGroundGammaObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    GammaGroundGammaObject hc ground 0 := ⟨1, fun _ => GammaGroundDefSet.univ hc ground ((volumeGammaSpace hc).power (Fin 0))⟩

theorem GammaGroundGammaObject.degree_zero_finite (A : GammaGroundGammaObject hc ground 0) : gammaGroundFiniteGammaProperty A := by
  intro i
  exact Set.Subsingleton.finite (fun x _ y _ => funext (fun j => j.elim0))

theorem GammaGroundGammaObject.product_finite (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l)
    (hA : gammaGroundFiniteGammaProperty A) (hB : gammaGroundFiniteGammaProperty B) : gammaGroundFiniteGammaProperty (A.product B) := by
  intro i
  apply (((hA (finProdFinEquiv.symm i).1).prod (hB (finProdFinEquiv.symm i).2)).image
    (fun p : (Fin k → Values.Gamma (M := M)) × (Fin l → Values.Gamma (M := M)) => Fin.append p.1 p.2)).subset
  rintro t ⟨a, ha⟩
  exact ⟨a.val, a.property, ha⟩

def GammaGroundFiniteGammaObject.product (A : GammaGroundFiniteGammaObject hc ground k) (B : GammaGroundFiniteGammaObject hc ground l) :
    GammaGroundFiniteGammaObject hc ground (k + l) := ⟨A.obj.product B.obj, A.obj.product_finite B.obj A.property B.property⟩

def GammaGroundFiniteGammaObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    GammaGroundFiniteGammaObject hc ground 0 := ⟨GammaGroundGammaObject.unit hc ground, (GammaGroundGammaObject.unit hc ground).degree_zero_finite⟩

end DiamondIntegral.Section3
