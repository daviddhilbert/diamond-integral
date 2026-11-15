import «section 5».NativeRectangleRowValues

/-! Exact original-domain presentations compute the native class of
the actual labelled RV object at the displayed parameter base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p k : ℕ} {sp : Fin p → SortTag}

theorem native_rv_row_value_of_presentation
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind) (z : Fin p → M)
    (U : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (D : GammaDomainFormula B p U.arity sp)
    (hD : {w | Fin.append z w ∈ D.val} = rawDomain U.domain) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z =
      nativeRVEvaluation h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) kind
          (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U)) := by
  let f := gammaGroundBijectionOfRawDomainEq (originalRVRowDomain hc D z) U.domain
    ((originalRVRowDomain_raw D z).trans hD)
  exact (nativeRVSetValue_bijection h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
    (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) kind _ _ f).trans
      ((nativeRVSetValue_object h00 linear hκ hs hc _ _ _ _ kind U).trans
        (nativeGroundRVEvaluation_class h00 linear hκ hs hc _ _ _ _ kind U))

end DiamondIntegral.Section5
