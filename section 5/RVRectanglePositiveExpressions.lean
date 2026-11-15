import «section 5».RESExpressionFiniteSums
import «section 5».NativeRectangleRowValues

/-! Signed rectangle contributions are differences of actual positive
RES expression families. Their row and total values use the same fixed
Euler integers and retain every residue torus factor. -/
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

def RVRectanglePieceSchema.resContribution (F : RVRectanglePieceSchema B p a sp) (m : ℕ) :
    (c : ℕ) × RESExpressionSchema B p sp c :=
  resExpressionCopies (resExpressionTorusTimes (.atom F.residue) F.freeArity).2 m

theorem RVRectanglePieceSchema.resContribution_valid
    (F : RVRectanglePieceSchema B p a sp) (m : ℕ) (z : Fin p → M) (hv : F.Valid hc z) :
    (F.resContribution m).2.Valid hc z :=
  resExpressionCopies_valid _ m z (resExpressionTorusTimes_valid (.atom F.residue) F.freeArity z hv.1)

theorem RVRectanglePieceSchema.resContribution_native_value
    (F : RVRectanglePieceSchema B p a sp) (m : ℕ) (z : Fin p → M) (hv : F.Valid hc z) :
    (F.resContribution m).2.nativeValue hc z (F.resContribution_valid m z hv) =
      (m : RESDimensionFreeReduction.Ring ⟨B.real ∪ Set.range z,B.gamma⟩) *
        (nativeTorusClass ⟨B.real ∪ Set.range z,B.gamma⟩ ^ F.freeArity *
          nativeRESChartClass (F.residue.chart hc z hv.1)) := by
  exact (resExpressionCopies_native_value _ m z
    (resExpressionTorusTimes_valid (.atom F.residue) F.freeArity z hv.1)).trans
      (congrArg (fun u => (m : RESDimensionFreeReduction.Ring ⟨B.real ∪ Set.range z,B.gamma⟩)*u)
        (resExpressionTorusTimes_native_value (.atom F.residue) F.freeArity z hv.1))

theorem RVRectanglePieceSchema.resContribution_total_formal_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : RVRectanglePieceSchema B p a (fun _ => .rv)) (m : ℕ)
    (hv : ∀ x : X, F.Valid hc (rvValues x.val)) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X (F.resContribution m).2.formalValue) =
      (m : RESDimensionFreeReduction.Ring B) * (nativeTorusClass B ^ F.freeArity *
        nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X F.residue.domain)) := by
  unfold resContribution
  rw [resExpressionCopies_total_formal_value,
    resExpressionTorusTimes_total_formal_value h00 linear hκ hs hr hγ hΓ kind X (.atom F.residue) F.freeArity
      (fun x => (hv x).1),
    (RESExpressionSchema.atom F.residue).total_formal_evaluate h00 linear hκ hs hr hγ hΓ kind X
      (fun x => (hv x).1)]
  rfl

def RVRectangleDecompositionSchema.positiveExpression
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D)
    (hc : CanonicalStructure.IsCanonical (M := M)) (kind : EulerKind) :
    (c : ℕ) × RESExpressionSchema B p sp c :=
  resExpressionFiniteSum (fun i => (W.cells i).resContribution (((W.cells i).euler.syntax hc).eulerValue kind).toNat)

def RVRectangleDecompositionSchema.negativeExpression
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D)
    (hc : CanonicalStructure.IsCanonical (M := M)) (kind : EulerKind) :
    (c : ℕ) × RESExpressionSchema B p sp c :=
  resExpressionFiniteSum (fun i => (W.cells i).resContribution (-((W.cells i).euler.syntax hc).eulerValue kind).toNat)

theorem RVRectangleDecompositionSchema.positiveExpression_valid
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D)
    (kind : EulerKind) (z : Fin p → M) (hv : W.Valid hc z) :
    (W.positiveExpression hc kind).2.Valid hc z :=
  resExpressionFiniteSum_valid _ z hv.1 (fun i => (W.cells i).resContribution_valid _ z (hv.2.1 i))

theorem RVRectangleDecompositionSchema.negativeExpression_valid
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D)
    (kind : EulerKind) (z : Fin p → M) (hv : W.Valid hc z) :
    (W.negativeExpression hc kind).2.Valid hc z :=
  resExpressionFiniteSum_valid _ z hv.1 (fun i => (W.cells i).resContribution_valid _ z (hv.2.1 i))

theorem RVRectangleDecompositionSchema.positive_negative_row_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D)
    (z : Fin p → M) (hv : W.Valid hc z) :
    (W.positiveExpression hc kind).2.nativeValue hc z (W.positiveExpression_valid kind z hv) -
      (W.negativeExpression hc kind).2.nativeValue hc z (W.negativeExpression_valid kind z hv) =
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z := by
  unfold positiveExpression negativeExpression
  rw [resExpressionFiniteSum_native_value _ z hv.1
      (fun i => (W.cells i).resContribution_valid _ z (hv.2.1 i)),
    resExpressionFiniteSum_native_value _ z hv.1
      (fun i => (W.cells i).resContribution_valid _ z (hv.2.1 i)),←Finset.sum_sub_distrib]
  exact (Finset.sum_congr rfl (fun i _ => by
    rw [(W.cells i).resContribution_native_value _ z (hv.2.1 i),
      (W.cells i).resContribution_native_value _ z (hv.2.1 i)]
    exact integer_positive_negative_weighted _ _ _)).trans
      (W.row_native_value h00 linear hκ hs hr hγ hΓ kind z hv).symm

theorem RVRectangleDecompositionSchema.positive_negative_total_formal_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    {D : GammaDomainFormula B p a (fun _ => .rv)} (W : RVRectangleDecompositionSchema D)
    (hv : ∀ x : X, W.Valid hc (rvValues x.val)) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X (W.positiveExpression hc kind).2.formalValue) -
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X (W.negativeExpression hc kind).2.formalValue) =
        nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X D) := by
  let ev := (nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X).comp
    (relativeRESFormalEvaluator X).toAddMonoidHom
  change ev (W.positiveExpression hc kind).2.formalValue - ev (W.negativeExpression hc kind).2.formalValue = _
  unfold positiveExpression negativeExpression
  rw [resExpressionFiniteSum_additive_evaluate,resExpressionFiniteSum_additive_evaluate,←Finset.sum_sub_distrib]
  exact (Finset.sum_congr rfl (fun i _ => by
    change nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X ((W.cells i).resContribution _).2.formalValue) -
      nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
        (relativeRESFormalEvaluator X ((W.cells i).resContribution _).2.formalValue) = _
    rw [(W.cells i).resContribution_total_formal_value h00 linear hκ hs hr hγ hΓ kind X _
      (fun x => (hv x).2.1 i),
      (W.cells i).resContribution_total_formal_value h00 linear hκ hs hr hγ hΓ kind X _
        (fun x => (hv x).2.1 i)]
    exact integer_positive_negative_weighted _ _ _)).trans
      (W.total_native_value h00 linear hκ hs hr hγ hΓ kind X hv).symm

end DiamondIntegral.Section5
