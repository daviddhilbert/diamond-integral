import «section 3».GammaGroundMeasuredRVScissors
import «section 3».GammaGroundRVProducts

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def gammaGroundMeasuredRVProductLeft (U : GammaGroundMeasuredRVObject hc ground k)
    (V : GammaGroundMeasuredRVObject hc ground l) :
    GammaGroundMap (U.underlying.product V.underlying).domain U.underlying.domain :=
  (GammaGroundMap.prodFst _ _).comp (gammaGroundRVUnpack _ _)

def gammaGroundMeasuredRVProductRight (U : GammaGroundMeasuredRVObject hc ground k)
    (V : GammaGroundMeasuredRVObject hc ground l) :
    GammaGroundMap (U.underlying.product V.underlying).domain V.underlying.domain :=
  (GammaGroundMap.prodSnd _ _).comp (gammaGroundRVUnpack _ _)

def GammaGroundMeasuredRVObject.product (U : GammaGroundMeasuredRVObject hc ground k)
    (V : GammaGroundMeasuredRVObject hc ground l) : GammaGroundMeasuredRVObject hc ground (k + l) where
  underlying := U.underlying.product V.underlying
  form := GammaGroundVolumeForm.mul (U.form.comp (gammaGroundMeasuredRVProductLeft U V))
    (V.form.comp (gammaGroundMeasuredRVProductRight U V))

@[simp] theorem GammaGroundMeasuredRVObject.product_form (U : GammaGroundMeasuredRVObject hc ground k)
    (V : GammaGroundMeasuredRVObject hc ground l) (a : (U.product V).underlying.domain) :
    gammaGroundFormValue (U.product V).form a =
      gammaGroundFormValue U.form (gammaGroundMeasuredRVProductLeft U V a) *
        gammaGroundFormValue V.form (gammaGroundMeasuredRVProductRight U V a) := rfl

theorem GammaGroundMeasuredRVObject.product_combined (U : GammaGroundMeasuredRVObject hc ground k)
    (V : GammaGroundMeasuredRVObject hc ground l) (a : (U.product V).underlying.domain) :
    (U.product V).combinedWeight a =
      U.combinedWeight (gammaGroundMeasuredRVProductLeft U V a) *
        V.combinedWeight (gammaGroundMeasuredRVProductRight U V a) := by
  unfold GammaGroundMeasuredRVObject.combinedWeight
  rw [GammaGroundMeasuredRVObject.product_form, Fin.prod_univ_add]
  have hleft : ∀ i : Fin k, (U.product V).underlying.target a (Fin.castAdd l i) =
      U.underlying.target (gammaGroundMeasuredRVProductLeft U V a) i := by
    intro i
    apply Subtype.ext
    change rvAppend _ _ (Fin.castAdd l i) = _
    exact Fin.append_left _ _ i
  have hright : ∀ i : Fin l, (U.product V).underlying.target a (Fin.natAdd k i) =
      V.underlying.target (gammaGroundMeasuredRVProductRight U V a) i := by
    intro i
    apply Subtype.ext
    change rvAppend _ _ (Fin.natAdd k i) = _
    exact Fin.append_right _ _ i
  simp only [hleft, hright]
  ac_rfl

end DiamondIntegral.Section3
