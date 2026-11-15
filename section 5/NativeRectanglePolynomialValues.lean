import «section 5».RVRectangleContributionPolynomials
import «section 5».GammaValuePowerTotals

/-! Formal rectangle certificates evaluate at the actual parameter base
and on total families. A full varying value torsor supplies every torus
factor, so these certificates can be transported by one preparation. -/
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
variable {p q a : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem additive_map_nat_mul {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+ S) (n : ℕ) (x : R) : f ((n : R)*x) = (n : S)*f x := by
  simpa only [nsmul_eq_mul] using f.map_nsmul n x

theorem RVRectangleDecompositionSchema.resPolynomial_native_value
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D)
    (T : GammaValueSchema B p sp) (c : Fin W.size → ℕ) (z : Fin p → M)
    (hw : W.Valid hc z) (ht : T.Valid hc z) :
    nativeSchemaEvaluator hc z (W.resPolynomial T.resSchema c) =
      ∑ i : Fin W.size, (c i : RESDimensionFreeReduction.Ring ⟨B.real ∪ Set.range z,B.gamma⟩) *
        (nativeRESChartClass ((W.cells i).residue.chart hc z (hw.2.1 i).1) *
          nativeTorusClass ⟨B.real ∪ Set.range z,B.gamma⟩ ^ (W.cells i).freeArity) := by
  unfold resPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hf := (RESExpressionSchema.atom (W.cells i).residue).formalValue_evaluate hc z (hw.2.1 i).1
  have ht' := (RESExpressionSchema.atom T.resSchema).formalValue_evaluate hc z ht.1
  have htorus : nativeRESChartClass (T.resSchema.chart hc z ht.1) =
      nativeTorusClass ⟨B.real ∪ Set.range z,B.gamma⟩ := T.native_fibre_equality hc z ht
  change nativeSchemaEvaluator hc z (FreeCommRing.of ⟨(W.cells i).residueArity,(W.cells i).residue⟩) =
    nativeRESChartClass ((W.cells i).residue.chart hc z (hw.2.1 i).1) at hf
  change nativeSchemaEvaluator hc z (FreeCommRing.of ⟨1,T.resSchema⟩) =
    nativeRESChartClass (T.resSchema.chart hc z ht.1) at ht'
  rw [map_mul,map_natCast,map_mul,map_pow,hf,ht',htorus]

theorem RVRectangleDecompositionSchema.resPolynomial_total_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    {D : GammaDomainFormula B p a (fun _ => .rv)} (W : RVRectangleDecompositionSchema D)
    (T : GammaValueSchema B p (fun _ => .rv)) (c : Fin W.size → ℕ)
    (ht : ∀ x : X, T.Valid hc (rvValues x.val)) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X (W.resPolynomial T.resSchema c)) =
      ∑ i : Fin W.size, (c i : RESDimensionFreeReduction.Ring B) *
        (nativeTorusClass B ^ (W.cells i).freeArity *
          nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
            (originalRVTotalFamily X (W.cells i).residue.domain)) := by
  unfold resPolynomial
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [(relativeRESFormalEvaluator X).map_mul,map_natCast,
    additive_map_nat_mul,nativeRESFormal_value_power_total h00 linear hκ hs hr hγ hΓ kind X _ T _ ht]

def RVRectangleDecompositionSchema.positivePolynomial
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D)
    (hc : CanonicalStructure.IsCanonical (M := M)) (kind : EulerKind) (T : RESSetSchema B p 1 sp) :=
  W.resPolynomial T (fun i => (((W.cells i).euler.syntax hc).eulerValue kind).toNat)

def RVRectangleDecompositionSchema.negativePolynomial
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D)
    (hc : CanonicalStructure.IsCanonical (M := M)) (kind : EulerKind) (T : RESSetSchema B p 1 sp) :=
  W.resPolynomial T (fun i => (-((W.cells i).euler.syntax hc).eulerValue kind).toNat)

theorem RVRectangleDecompositionSchema.positive_negative_polynomial_row_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D)
    (T : GammaValueSchema B p sp) (z : Fin p → M) (hw : W.Valid hc z) (ht : T.Valid hc z) :
    nativeSchemaEvaluator hc z (W.positivePolynomial hc kind T.resSchema) -
      nativeSchemaEvaluator hc z (W.negativePolynomial hc kind T.resSchema) =
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z := by
  unfold positivePolynomial negativePolynomial
  rw [W.resPolynomial_native_value T _ z hw ht,W.resPolynomial_native_value T _ z hw ht,
    ←Finset.sum_sub_distrib]
  exact (Finset.sum_congr rfl (fun i _ => by
    rw [mul_comm (nativeRESChartClass _)]
    exact integer_positive_negative_weighted _ _ _)).trans
      (W.row_native_value h00 linear hκ hs hr hγ hΓ kind z hw).symm

theorem RVRectangleDecompositionSchema.positivePolynomial_recode
    (R : GammaParameterRecode B p q sp sq) {D : GammaDomainFormula B p a sp}
    (W : RVRectangleDecompositionSchema D) (hc : CanonicalStructure.IsCanonical (M := M))
    (kind : EulerKind) (T : RESSetSchema B p 1 sp) :
    (W.recode R).positivePolynomial hc kind (T.recode R) = formalSchemaRecode R (W.positivePolynomial hc kind T) := by
  unfold positivePolynomial
  rw [W.resPolynomial_recode R]
  congr 1
  funext i
  exact congrArg Int.toNat ((W.cells i).euler.recode_eulerValue hc R kind)

theorem RVRectangleDecompositionSchema.negativePolynomial_recode
    (R : GammaParameterRecode B p q sp sq) {D : GammaDomainFormula B p a sp}
    (W : RVRectangleDecompositionSchema D) (hc : CanonicalStructure.IsCanonical (M := M))
    (kind : EulerKind) (T : RESSetSchema B p 1 sp) :
    (W.recode R).negativePolynomial hc kind (T.recode R) = formalSchemaRecode R (W.negativePolynomial hc kind T) := by
  unfold negativePolynomial
  rw [W.resPolynomial_recode R]
  congr 1
  funext i
  exact congrArg (fun e : ℤ => (-e).toNat) ((W.cells i).euler.recode_eulerValue hc R kind)

end DiamondIntegral.Section5
