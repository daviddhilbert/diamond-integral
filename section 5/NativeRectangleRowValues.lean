import «section 5».OriginalRVRowBijections
import «section 5».RelativeRESProductClasses
import «section 5».RVRectangleTotalValues
import «section 5».OriginalGammaRVRowPresentations
import «section 5».NativeUnitGammaValues

/-! Complete rectangle schemata compute the actual native value of each
row over its exact parameter base, retaining all RV representatives. -/
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
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a : ℕ} {sp : Fin p → SortTag}
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)

def nativeRVRowValue (D : GammaDomainFormula B p a sp) (z : Fin p → M) :
    RESDimensionFreeReduction.Ring ⟨B.real ∪ Set.range z,B.gamma⟩ :=
  nativeRVSetValue h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
    (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl)
    kind (originalRVRowDomain hc D z)

theorem RESSetSchema.native_row_value (F : RESSetSchema B p a sp) (z : Fin p → M) (hv : F.Valid hc z) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind F.domain z = nativeRESChartClass (F.chart hc z hv) := by
  unfold nativeRVRowValue
  have hb : GammaGroundBijection (originalRVRowDomain hc F.domain z) (F.object hc z hv).obj.domain :=
    gammaGroundBijectionOfCarrierEq _ _ rfl
  have he := nativeRVSetValue_bijection h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
    (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) kind _ _ hb
  rw [nativeRVSetValue_object,nativeGroundRVEvaluation_class] at he
  refine he.trans ?_
  change nativeRVEvaluation h00 linear hκ hs hc _ _ _ _ kind
    (RVOrdinaryRing.objectClass (F.chart hc z hv).toChart) = _
  rw [←RVOrdinaryMaps.ofRES_class,nativeRVEvaluation_res]
  rfl

theorem original_gamma_row_value {n : ℕ}
    (D : GammaDomainFormula B p n sp) (C : OriginalEulerCertificate B sp n)
    (z : Fin p → M) (hv : C.ValidFor hc D z) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z =
      nativeTorusClass ⟨B.real ∪ Set.range z,B.gamma⟩ ^ n *
        ((C.syntax hc).eulerValue kind : RESDimensionFreeReduction.Ring ⟨B.real ∪ Set.range z,B.gamma⟩) := by
  have hD : originalGammaSourceValid hc D z :=
    (C.syntax hc).source_quotient_validity (nativeGammaRelationSyntax hc).proper
      (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less _ _ hv
  let I := Section3GammaCodeBridge.native hc (originalGammaSourceRow hc D z)
    (originalGammaSourceRow_definable hc D z hD)
  have hb := (gammaGroundRVUnitGammaCodeBijection I).symm.comp
    (originalGammaRVRowBijection D z I (originalGammaSourceRow_represents hc D z hD))
  unfold nativeRVRowValue
  rw [nativeRVSetValue_raw_unit_bijection h00 linear hκ hs _ _ _ kind _ _ hb,nativeUnitRVSetValue_gamma]
  have he := C.originalGammaRowEulerValue hc h00 hκ hs hr hγ D z hv kind
  unfold originalGammaRowEulerValue at he
  rw [dif_pos hD] at he
  exact (congrArg (fun c : ℤ => (c : RESDimensionFreeReduction.Ring ⟨B.real ∪ Set.range z,B.gamma⟩) *
    nativeTorusClass ⟨B.real ∪ Set.range z,B.gamma⟩ ^ n) he).trans (mul_comm _ _)

theorem RVRectanglePieceSchema.row_native_value
    (F : RVRectanglePieceSchema B p a sp) (z : Fin p → M) (hv : F.Valid hc z) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind F.source z =
      nativeTorusClass ⟨B.real ∪ Set.range z,B.gamma⟩ ^ F.freeArity *
        ((F.euler.syntax hc).eulerValue kind : RESDimensionFreeReduction.Ring ⟨B.real ∪ Set.range z,B.gamma⟩) *
          nativeRESChartClass (F.residue.chart hc z hv.1) := by
  have hb := (originalRVRowProductBijection (hc := hc) F.residue.domain F.gamma z).comp
    (originalRVRowBijection (hc := hc) F.source F.target F.graph z hv.2.2)
  have he := nativeRVSetValue_bijection h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
    (small_union_range_carrier hκ B.real hr z) hγ
    (hΓ.mono Set.subset_union_left Set.Subset.rfl) kind _ _ hb
  rw [nativeRVSetValue_product] at he
  change nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind F.source z =
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind F.residue.domain z *
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind F.gamma z at he
  rw [F.residue.native_row_value h00 linear hκ hs hr hγ hΓ kind z hv.1,
    original_gamma_row_value h00 linear hκ hs hr hγ hΓ kind F.gamma F.euler z hv.2.1] at he
  exact he.trans (by ring)

theorem RVRectangleDecompositionSchema.row_native_value
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D)
    (z : Fin p → M) (hv : W.Valid hc z) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z =
      ∑ i : Fin W.size, nativeTorusClass ⟨B.real ∪ Set.range z,B.gamma⟩ ^ (W.cells i).freeArity *
        (((W.cells i).euler.syntax hc).eulerValue kind : RESDimensionFreeReduction.Ring ⟨B.real ∪ Set.range z,B.gamma⟩) *
          nativeRESChartClass ((W.cells i).residue.chart hc z (hv.2.1 i).1) := by
  let A := fun i => originalRVRowDomain hc (W.cells i).source z
  have hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hv.2.2.2 i j hij (rvValues x) ⟨hi,hj⟩
  have hcov : ∀ x, x ∈ (originalRVRowDomain hc D z).carrier ↔ ∃ i, x ∈ (A i).carrier := by
    intro x
    exact hv.2.2.1 (rvValues x)
  have he := nativeRVSetValue_finite_partition h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
    (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl)
    kind (originalRVRowDomain hc D z) A hd hcov
  exact he.trans (Finset.sum_congr rfl (fun i _ =>
    (W.cells i).row_native_value h00 linear hκ hs hr hγ hΓ kind z (hv.2.1 i)))

end DiamondIntegral.Section5
