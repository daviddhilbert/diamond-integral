import «section 5».RVRectanglePositiveExpressions
import «section 5».NativeRESFamilyFubini

/-! Pointwise equality of actual native RV row values implies equality
of total values whenever complete rectangle packages are fixed. The
comparison is reduced to actual positive RES families. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

theorem native_rv_rectangle_family_fubini
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    {D : GammaDomainFormula B p a (fun _ => .rv)} {E : GammaDomainFormula B p b (fun _ => .rv)}
    (W : RVRectangleDecompositionSchema D) (V : RVRectangleDecompositionSchema E)
    (hw : ∀ x : X, W.Valid hc (rvValues x.val)) (hv : ∀ x : X, V.Valid hc (rvValues x.val))
    (he : ∀ x : X, nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D (rvValues x.val) =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind E (rvValues x.val)) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X D) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X E) := by
  let P := W.positiveExpression hc kind
  let Q := W.negativeExpression hc kind
  let P' := V.positiveExpression hc kind
  let Q' := V.negativeExpression hc kind
  let F := P.2.sum Q'.2
  let G := Q.2.sum P'.2
  have hf (x : X) : F.Valid hc (rvValues x.val) :=
    ⟨W.positiveExpression_valid kind _ (hw x),V.negativeExpression_valid kind _ (hv x)⟩
  have hg (x : X) : G.Valid hc (rvValues x.val) :=
    ⟨W.negativeExpression_valid kind _ (hw x),V.positiveExpression_valid kind _ (hv x)⟩
  have hpoint (x : X) :
      nativeRESChartClass (F.setSchema.chart hc (rvValues x.val) (F.setSchema_valid hc _ (hf x))) =
      nativeRESChartClass (G.setSchema.chart hc (rvValues x.val) (G.setSchema_valid hc _ (hg x))) := by
    rw [F.nativeClass_eq hc _ (hf x),G.nativeClass_eq hc _ (hg x)]
    have hr := (W.positive_negative_row_value h00 linear hκ hs hr hγ hΓ kind _ (hw x)).trans
      ((he x).trans (V.positive_negative_row_value h00 linear hκ hs hr hγ hΓ kind _ (hv x)).symm)
    exact (sub_eq_sub_iff_add_eq_add.mp hr).trans (add_comm _ _)
  have ht := native_res_family_fubini h00 linear hκ hs hr hγ hΓ kind X F.setSchema G.setSchema
    (fun x => F.setSchema_valid hc _ (hf x)) (fun x => G.setSchema_valid hc _ (hg x)) hpoint
  let ev := (nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X).comp
    (relativeRESFormalEvaluator X).toAddMonoidHom
  have hsums : ev F.formalValue = ev G.formalValue :=
    (F.total_formal_evaluate h00 linear hκ hs hr hγ hΓ kind X hf).trans
      (ht.trans (G.total_formal_evaluate h00 linear hκ hs hr hγ hΓ kind X hg).symm)
  change ev (P.2.formalValue+Q'.2.formalValue) = ev (Q.2.formalValue+P'.2.formalValue) at hsums
  rw [ev.map_add,ev.map_add] at hsums
  have hdiff : ev P.2.formalValue - ev Q.2.formalValue = ev P'.2.formalValue - ev Q'.2.formalValue :=
    sub_eq_sub_iff_add_eq_add.mpr (hsums.trans (add_comm _ _))
  exact (W.positive_negative_total_formal_value h00 linear hκ hs hr hγ hΓ kind X hw).symm.trans
    (hdiff.trans (V.positive_negative_total_formal_value h00 linear hκ hs hr hγ hΓ kind X hv))

end DiamondIntegral.Section5
