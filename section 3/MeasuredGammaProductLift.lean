import «section 3».GammaRVProductCodeMaps
import «section 3».MeasuredGammaProducts
import «section 3».MeasuredRVProductLaws
import «section 3».MeasuredRVIsomorphismClasses

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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

theorem measuredGammaProduct_combined (A : MeasuredGammaObject hc S k) (B : MeasuredGammaObject hc S l)
    (i : Fin (A.underlying.tags * B.underlying.tags))
    (a : A.underlying.piece (finProdFinEquiv.symm i).1)
    (b : B.underlying.piece (finProdFinEquiv.symm i).2) :
    (A.product B).combinedWeight ⟨i, (gammaAppendBijection (A.underlying.piece (finProdFinEquiv.symm i).1)
        (B.underlying.piece (finProdFinEquiv.symm i).2)).map ⟨(a.val, b.val), a.property, b.property⟩⟩ =
      A.combinedWeight ⟨(finProdFinEquiv.symm i).1, a⟩ *
        B.combinedWeight ⟨(finProdFinEquiv.symm i).2, b⟩ := by
  let P := A.underlying.piece (finProdFinEquiv.symm i).1
  let Q := B.underlying.piece (finProdFinEquiv.symm i).2
  have hl : gammaProductLeft P Q ((gammaAppendBijection P Q).map ⟨(a.val, b.val), a.property, b.property⟩) = a := by
    change Map.prodFst P Q ((gammaAppendBijection P Q).symm.map
      ((gammaAppendBijection P Q).map ⟨(a.val, b.val), a.property, b.property⟩)) = a
    rw [DefinableBijection.symm_apply_apply]
    rfl
  have hr : gammaProductRight P Q ((gammaAppendBijection P Q).map ⟨(a.val, b.val), a.property, b.property⟩) = b := by
    change Map.prodSnd P Q ((gammaAppendBijection P Q).symm.map
      ((gammaAppendBijection P Q).map ⟨(a.val, b.val), a.property, b.property⟩)) = b
    rw [DefinableBijection.symm_apply_apply]
    rfl
  unfold MeasuredGammaObject.combinedWeight MeasuredGammaObject.weight
  change (gammaFormValue (A.form _) (gammaProductLeft P Q ((gammaAppendBijection P Q).map ⟨(a.val, b.val), a.property, b.property⟩)) *
    gammaFormValue (B.form _) (gammaProductRight P Q ((gammaAppendBijection P Q).map ⟨(a.val, b.val), a.property, b.property⟩))) *
    (∏ j, (Fin.append a.val b.val j : Values.Gamma (M := M))) = _
  rw [hl, hr, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  ac_rfl

theorem measuredGammaProduct_combined_code (A : MeasuredGammaObject hc S k) (B : MeasuredGammaObject hc S l)
    (i : Fin (A.underlying.tags * B.underlying.tags))
    (a : codePreimage (A.underlying.piece (finProdFinEquiv.symm i).1))
    (b : codePreimage (B.underlying.piece (finProdFinEquiv.symm i).2)) :
    (A.product B).combinedWeight ((A.product B).underlying.decode ⟨i, gammaProductCode _ _ a b⟩) =
      A.combinedWeight (A.underlying.decode ⟨(finProdFinEquiv.symm i).1, a⟩) *
        B.combinedWeight (B.underlying.decode ⟨(finProdFinEquiv.symm i).2, b⟩) := by
  have he : (A.product B).underlying.decode ⟨i, gammaProductCode _ _ a b⟩ =
      ⟨i, (gammaAppendBijection _ _).map
        ⟨((codeDecode _ a).val, (codeDecode _ b).val), (codeDecode _ a).property, (codeDecode _ b).property⟩⟩ := by
    apply congrArg (fun p : (A.product B).underlying.piece i => (⟨i, p⟩ : (A.product B).underlying.Carrier))
    apply Subtype.ext
    exact gammaCodeAppend_decode a.val b.val
  rw [he]
  exact measuredGammaProduct_combined A B i (codeDecode _ a) (codeDecode _ b)

def measuredGammaProductLiftHom (A : MeasuredGammaObject hc S k) (B : MeasuredGammaObject hc S l) :
    MeasuredRVHom (A.product B).rvLift (A.rvLift.product hc B.rvLift) where
  bijection := gammaRVProductBijection A.underlying B.underlying
  preserves x := by
    obtain ⟨⟨i, c⟩, rfl⟩ := (A.product B).underlying.rvEncodeCode_surjective x
    obtain ⟨a, b, rfl⟩ := gammaProductCode_surjective
      (A.underlying.piece (finProdFinEquiv.symm i).1)
      (B.underlying.piece (finProdFinEquiv.symm i).2) c
    change _ = (A.rvLift.product hc B.rvLift).combinedWeight
      ((gammaRVProductBijection A.underlying B.underlying).map _)
    have he := gammaRVProductBijection_code A.underlying B.underlying
      (show Fin (A.underlying.tags * B.underlying.tags) from i) a b
    calc
      _ = (A.product B).combinedWeight ((A.product B).underlying.decode
          ⟨i, gammaProductCode _ _ a b⟩) := measuredGammaLift_combined _ _
      _ = A.combinedWeight (A.underlying.decode ⟨(finProdFinEquiv.symm i).1, a⟩) *
          B.combinedWeight (B.underlying.decode ⟨(finProdFinEquiv.symm i).2, b⟩) :=
        measuredGammaProduct_combined_code A B i a b
      _ = A.rvLift.combinedWeight (A.underlying.rvEncodeCode ⟨(finProdFinEquiv.symm i).1, a⟩) *
          B.rvLift.combinedWeight (B.underlying.rvEncodeCode ⟨(finProdFinEquiv.symm i).2, b⟩) := by
        rw [measuredGammaLift_combined, measuredGammaLift_combined]
      _ = (A.rvLift.product hc B.rvLift).combinedWeight
          (rvPackPair A.rvLift.underlying.domain B.rvLift.underlying.domain
            (A.underlying.rvEncodeCode ⟨(finProdFinEquiv.symm i).1, a⟩)
            (B.underlying.rvEncodeCode ⟨(finProdFinEquiv.symm i).2, b⟩)) :=
        (MeasuredRVObject.product_combined_pair hc A.rvLift B.rvLift _ _).symm
      _ = _ := congrArg (A.rvLift.product hc B.rvLift).combinedWeight he.symm

theorem measuredGammaRVClass_product (A : MeasuredGammaObject hc S k) (B : MeasuredGammaObject hc S l) :
    measuredRVClass hc (A.product B).rvLift = measuredRVClass hc (A.rvLift.product hc B.rvLift) :=
  measuredRVClass_iso hc (asIso (show (A.product B).rvLift ⟶ A.rvLift.product hc B.rvLift from
    measuredGammaProductLiftHom A B))

def measuredGammaUnitLiftHom :
    MeasuredRVHom (MeasuredGammaObject.unit hc S).rvLift (MeasuredRVObject.unit (M := M) hc S) where
  bijection := gammaRVUnitBijection
  preserves x := by
    obtain ⟨c, rfl⟩ := (MeasuredGammaObject.unit hc S).underlying.rvEncodeCode_surjective x
    rw [measuredGammaLift_combined, MeasuredRVObject.unit_combinedWeight]
    change gammaFormValue (gammaOneForm hc _) _ * (∏ j : Fin 0, _) = 1
    rw [gammaOneForm_value, Fin.prod_univ_zero, mul_one]

theorem measuredGammaRVClass_unit :
    measuredRVClass hc (MeasuredGammaObject.unit hc S).rvLift =
      measuredRVClass hc (MeasuredRVObject.unit (M := M) hc S) :=
  measuredRVClass_iso hc (asIso (show (MeasuredGammaObject.unit hc S).rvLift ⟶ MeasuredRVObject.unit hc S from
    measuredGammaUnitLiftHom))

end DiamondIntegral.Section3
