import «section 5».OriginalConstantRVDomains
import «section 5».NativeRVRealExtensions
import «section 5».NativeRectangleRowValues
import «section 5».NativeRVSetArithmetic

/-! Geometric denominator clearing is represented by literal original-
ground RV-domain products. Their intrinsic fibre values are exactly the
required affine powers; the finite padding degree is genuine witness data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

def originalPaddedRVDomain (hc : CanonicalStructure.IsCanonical (M := M))
    (D : GammaDomainFormula B p a sp) (r : ℕ) :
    GammaDomainFormula B p (a+(nativeAffineRVPower hc B r).arity) sp :=
  originalDomainProduct D (originalConstantRVDomain (nativeAffineRVPower hc B r).domain sp)

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem nativeAffineConstant_row_value (kind : EulerKind) (r : ℕ)
    (z : Fin p → M) (hz : ∀ i,sortEval (sp i) (z i)) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind
      (originalConstantRVDomain (nativeAffineRVPower hc B r).domain sp) z =
      RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)) ^ r := by
  let Q := nativeAffineRVPower hc B r
  let D := (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M))
  let hsmall := small_union_range_carrier hκ B.real hr z
  let hnontriv : Section2.NontrivialDefinableGamma D := hΓ.mono Set.subset_union_left Set.Subset.rfl
  refine (nativeRVSetValue_bijection h00 linear hκ hs hc D hsmall hγ hnontriv kind _ _
    (originalConstantRVRowBijection Q.domain sp z hz)).trans ?_
  exact (nativeRVSetValue_object h00 linear hκ hs hc D hsmall hγ hnontriv kind
    (nativeRVObjectMonoReal Set.subset_union_left Q)).trans
      (nativeAffineRVPower_monoReal_raw_value Set.subset_union_left h00 linear hκ hs hsmall hγ hnontriv kind r)

theorem nativePaddedRV_row_value (kind : EulerKind)
    (D : GammaDomainFormula B p a sp) (r : ℕ) (z : Fin p → M) (hz : ∀ i,sortEval (sp i) (z i)) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (originalPaddedRVDomain hc D r) z =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z *
        RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)) ^ r := by
  let Q := originalConstantRVDomain (nativeAffineRVPower hc B r).domain sp
  let Dbase := (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M))
  let hsmall := small_union_range_carrier hκ B.real hr z
  let hnontriv : Section2.NontrivialDefinableGamma Dbase := hΓ.mono Set.subset_union_left Set.Subset.rfl
  have he := nativeRVSetValue_bijection h00 linear hκ hs hc Dbase hsmall hγ hnontriv kind _ _
    (originalRVRowProductBijection (hc := hc) D Q z)
  refine he.trans ?_
  rw [nativeRVSetValue_product]
  exact congrArg (nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z * ·)
    (nativeAffineConstant_row_value h00 linear hκ hs hr hγ hΓ kind r z hz)

theorem geometricRowValue_eq_iff_padded
    (D : GammaDomainFormula B p a sp) (E : GammaDomainFormula B p b sp)
    (k l : ℕ) (z : Fin p → M) (hz : ∀ i,sortEval (sp i) (z i)) :
    geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)))
        (nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric D z) k =
      geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)))
        (nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric E z) l ↔
      ∃ N : ℕ,k ≤ N ∧ l ≤ N ∧
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric (originalPaddedRVDomain hc D (N-k)) z =
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric (originalPaddedRVDomain hc E (N-l)) z := by
  simp only [geometricDegreeValue_eq_iff,nativePaddedRV_row_value h00 linear hκ hs hr hγ hΓ .geometric _ _ z hz,mul_comm]

end DiamondIntegral.Section5
