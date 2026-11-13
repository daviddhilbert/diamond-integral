import «section 3».RVProducts
import «section 3».RVSemiring
import «section 3».RVFormGraphs
import «section 3».GammaFormOperations

/-! Actual cartesian products for the pointwise Gamma-measured RV
category. The volume is the product of the pulled-back forms. Arrow
preservation is checked everywhere through the combined-weight equation. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

theorem RVObject.target_product (U : RVObject (M := M) S k) (V : RVObject (M := M) S l)
    (a : (U.product V).domain) :
    (U.product V).target a = Fin.append (U.target (rvProductLeft U V a)) (V.target (rvProductRight U V a)) := by
  funext i
  apply Subtype.ext
  change rvAppend (U.volume (rvProductLeft U V a)).val (V.volume (rvProductRight U V a)).val i =
    (Fin.append (U.target (rvProductLeft U V a)) (V.target (rvProductRight U V a)) i).val
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [rvAppend, Fin.append_left, Fin.append_right] <;> rfl

def MeasuredRVObject.product (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) (V : MeasuredRVObject (M := M) S l) :
    MeasuredRVObject S (k + l) where
  underlying := U.underlying.product V.underlying
  form := GammaVolumeForm.toRVVolumeForm hc (GammaVolumeForm.mul
    ((U.form.toGammaVolumeForm hc).comp (rvProductLeft U.underlying V.underlying))
    ((V.form.toGammaVolumeForm hc).comp (rvProductRight U.underlying V.underlying)))

@[simp] theorem MeasuredRVObject.product_form (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) (V : MeasuredRVObject (M := M) S l)
    (a : (U.product hc V).underlying.domain) :
    (U.product hc V).form.toFun a =
      U.form.toFun (rvProductLeft U.underlying V.underlying a) *
      V.form.toFun (rvProductRight U.underlying V.underlying a) := rfl

theorem MeasuredRVObject.product_combinedWeight (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) (V : MeasuredRVObject (M := M) S l)
    (a : (U.product hc V).underlying.domain) :
    (U.product hc V).combinedWeight a =
      U.combinedWeight (rvProductLeft U.underlying V.underlying a) *
      V.combinedWeight (rvProductRight U.underlying V.underlying a) := by
  unfold MeasuredRVObject.combinedWeight
  rw [MeasuredRVObject.product_form]
  have he := RVObject.target_product U.underlying V.underlying a
  change (U.form.toFun _ * V.form.toFun _) *
    (∏ i, Section2.rvFiniteValue ((U.underlying.product V.underlying).target a i)) = _
  rw [he, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  ac_rfl

def measuredRVProductHom (hc : CanonicalStructure.IsCanonical (M := M))
    {U U' : MeasuredRVObject (M := M) S k} {V V' : MeasuredRVObject (M := M) S l}
    (f : MeasuredRVHom U U') (g : MeasuredRVHom V V') :
    MeasuredRVHom (U.product hc V) (U'.product hc V') where
  bijection := rvProductBijection f.bijection g.bijection
  preserves a := by
    calc
      _ = U.combinedWeight (rvProductLeft U.underlying V.underlying a) *
          V.combinedWeight (rvProductRight U.underlying V.underlying a) :=
        MeasuredRVObject.product_combinedWeight hc U V a
      _ = U'.combinedWeight (f.bijection.map (rvProductLeft U.underlying V.underlying a)) *
          V'.combinedWeight (g.bijection.map (rvProductRight U.underlying V.underlying a)) :=
        congrArg₂ (fun x y : Section2.Gamma M => x * y) (f.preserves _) (g.preserves _)
      _ = _ :=
        (congrArg₂ (fun x y : Section2.Gamma M => x * y)
          (congrArg U'.combinedWeight (rvProductLeft_map f.bijection g.bijection a)).symm
          (congrArg V'.combinedWeight (rvProductRight_map f.bijection g.bijection a)).symm).trans
            (MeasuredRVObject.product_combinedWeight hc U' V' _).symm

def MeasuredRVObject.withZeroForm (hc : CanonicalStructure.IsCanonical (M := M))
    (U : RVObject (M := M) S k) : MeasuredRVObject S k :=
  ⟨U, (gammaOneForm hc U.domain).toRVVolumeForm hc⟩

@[simp] theorem MeasuredRVObject.withZeroForm_value (hc : CanonicalStructure.IsCanonical (M := M))
    (U : RVObject (M := M) S k) (a : U.domain) :
    (MeasuredRVObject.withZeroForm hc U).form.toFun a = 1 := rfl

def MeasuredRVObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    MeasuredRVObject (M := M) S 0 := MeasuredRVObject.withZeroForm hc (RVObject.unit S)

end DiamondIntegral.Section3
