import «section 3».GammaGroundGammaProductDecomposition
import «section 3».GammaGroundMeasuredGammaProducts
import «section 3».GammaGroundGammaCodeFormRestrictions
/-! The measured Gamma lift respects cartesian products pointwise. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

theorem gammaGroundMeasuredGammaProduct_combined (A : GammaGroundMeasuredGammaObject hc ground k) (B : GammaGroundMeasuredGammaObject hc ground l)
    (i : Fin (A.underlying.tags * B.underlying.tags))
    (a : A.underlying.piece (finProdFinEquiv.symm i).1)
    (b : B.underlying.piece (finProdFinEquiv.symm i).2) :
    (A.product B).combinedWeight ⟨i, (gammaGroundGammaAppendBijection (A.underlying.piece (finProdFinEquiv.symm i).1)
        (B.underlying.piece (finProdFinEquiv.symm i).2)).map ⟨(a.val, b.val), a.property, b.property⟩⟩ =
      A.combinedWeight ⟨(finProdFinEquiv.symm i).1, a⟩ *
        B.combinedWeight ⟨(finProdFinEquiv.symm i).2, b⟩ := by
  let P := A.underlying.piece (finProdFinEquiv.symm i).1
  let Q := B.underlying.piece (finProdFinEquiv.symm i).2
  have hl : gammaGroundGammaProductLeft P Q ((gammaGroundGammaAppendBijection P Q).map ⟨(a.val, b.val), a.property, b.property⟩) = a := by
    change GammaGroundMap.prodFst P Q ((gammaGroundGammaAppendBijection P Q).symm.map
      ((gammaGroundGammaAppendBijection P Q).map ⟨(a.val, b.val), a.property, b.property⟩)) = a
    rw [GammaGroundBijection.symm_apply_apply]
    rfl
  have hr : gammaGroundGammaProductRight P Q ((gammaGroundGammaAppendBijection P Q).map ⟨(a.val, b.val), a.property, b.property⟩) = b := by
    change GammaGroundMap.prodSnd P Q ((gammaGroundGammaAppendBijection P Q).symm.map
      ((gammaGroundGammaAppendBijection P Q).map ⟨(a.val, b.val), a.property, b.property⟩)) = b
    rw [GammaGroundBijection.symm_apply_apply]
    rfl
  unfold GammaGroundMeasuredGammaObject.combinedWeight GammaGroundMeasuredGammaObject.weight
  change (gammaGroundFormValue (A.form _) (gammaGroundGammaProductLeft P Q ((gammaGroundGammaAppendBijection P Q).map ⟨(a.val, b.val), a.property, b.property⟩)) *
    gammaGroundFormValue (B.form _) (gammaGroundGammaProductRight P Q ((gammaGroundGammaAppendBijection P Q).map ⟨(a.val, b.val), a.property, b.property⟩))) *
    (∏ j, (Fin.append a.val b.val j : Values.Gamma (M := M))) = _
  rw [hl, hr, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  ac_rfl

theorem gammaGroundMeasuredGammaProduct_combined_code (A : GammaGroundMeasuredGammaObject hc ground k) (B : GammaGroundMeasuredGammaObject hc ground l)
    (i : Fin (A.underlying.tags * B.underlying.tags))
    (a : gammaGroundCodePreimage (A.underlying.piece (finProdFinEquiv.symm i).1))
    (b : gammaGroundCodePreimage (B.underlying.piece (finProdFinEquiv.symm i).2)) :
    (A.product B).combinedWeight ((A.product B).underlying.decode ⟨i, gammaGroundGammaProductCode _ _ a b⟩) =
      A.combinedWeight (A.underlying.decode ⟨(finProdFinEquiv.symm i).1, a⟩) *
        B.combinedWeight (B.underlying.decode ⟨(finProdFinEquiv.symm i).2, b⟩) := by
  have he : (A.product B).underlying.decode ⟨i, gammaGroundGammaProductCode _ _ a b⟩ =
      ⟨i, (gammaGroundGammaAppendBijection _ _).map
        ⟨((gammaGroundCodeDecode _ a).val, (gammaGroundCodeDecode _ b).val), (gammaGroundCodeDecode _ a).property, (gammaGroundCodeDecode _ b).property⟩⟩ := by
    apply congrArg (fun p : (A.product B).underlying.piece i => (⟨i, p⟩ : (A.product B).underlying.Carrier))
    apply Subtype.ext
    exact gammaCodeAppend_decode a.val b.val
  rw [he]
  exact gammaGroundMeasuredGammaProduct_combined A B i (gammaGroundCodeDecode _ a) (gammaGroundCodeDecode _ b)

end DiamondIntegral.Section3
