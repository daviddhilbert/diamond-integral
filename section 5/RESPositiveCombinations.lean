import «section 5».RESRelationTotalValues
import «section 5».GammaConstantValueSchemata

/-! Finite copies and retained residue torus factors are actual positive
RES expressions, with their fibre classes and absolute total values. -/
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

theorem nativeTorusSchema_valid (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i)) :
    (nativeTorusSchema B sp).Valid hc z :=
  (GammaValueSchema.constant_valid hc 1 (GammaGroupNames.one_definable_base B) z hz).1

theorem nativeTorusSchema_native_class (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i)) :
    nativeRESChartClass ((nativeTorusSchema B sp).chart hc z (nativeTorusSchema_valid z hz)) =
      nativeTorusClass ⟨B.real ∪ Set.range z,B.gamma⟩ :=
  (GammaValueSchema.constant 1 (GammaGroupNames.one_definable_base B)).native_fibre_equality hc z
    (GammaValueSchema.constant_valid hc 1 (GammaGroupNames.one_definable_base B) z hz)

def resExpressionCopies (E : RESExpressionSchema B p sp a) :
    ℕ → (c : ℕ) × RESExpressionSchema B p sp c
  | 0 => ⟨0,.empty⟩
  | n+1 => let C := resExpressionCopies E n; ⟨1+(a+C.1),.sum E C.2⟩

theorem resExpressionCopies_valid (E : RESExpressionSchema B p sp a) (n : ℕ)
    (z : Fin p → M) (hv : E.Valid hc z) : (resExpressionCopies E n).2.Valid hc z := by
  induction n with
  | zero => exact (E.setSchema_valid hc z hv).1
  | succ n ih => exact ⟨hv,ih⟩

theorem resExpressionCopies_native_value (E : RESExpressionSchema B p sp a) (n : ℕ)
    (z : Fin p → M) (hv : E.Valid hc z) :
    (resExpressionCopies E n).2.nativeValue hc z (resExpressionCopies_valid E n z hv) =
      (n : RESDimensionFreeReduction.Ring ⟨B.real ∪ Set.range z,B.gamma⟩) * E.nativeValue hc z hv := by
  induction n with
  | zero => simp only [resExpressionCopies,RESExpressionSchema.nativeValue,Nat.cast_zero,zero_mul]
  | succ n ih =>
    change E.nativeValue hc z hv + (resExpressionCopies E n).2.nativeValue hc z _ = _
    rw [ih,Nat.cast_succ,add_mul,one_mul,add_comm]

theorem resExpressionCopies_total_formal_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (E : RESExpressionSchema B p (fun _ => .rv) a) (n : ℕ) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X (resExpressionCopies E n).2.formalValue) =
    (n : RESDimensionFreeReduction.Ring B) *
      nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
        (relativeRESFormalEvaluator X E.formalValue) := by
  induction n with
  | zero => simp only [resExpressionCopies,RESExpressionSchema.formalValue,map_zero,Nat.cast_zero,zero_mul]
  | succ n ih =>
    change nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X (E.formalValue + (resExpressionCopies E n).2.formalValue)) = _
    simp only [map_add,ih,Nat.cast_succ,add_mul,one_mul,add_comm]

def resExpressionTorusTimes (E : RESExpressionSchema B p sp a) :
    ℕ → (c : ℕ) × RESExpressionSchema B p sp c
  | 0 => ⟨a,E⟩
  | n+1 => let C := resExpressionTorusTimes E n; ⟨1+C.1,.product C.2 (.atom (nativeTorusSchema B sp))⟩

theorem resExpressionTorusTimes_valid (E : RESExpressionSchema B p sp a) (n : ℕ)
    (z : Fin p → M) (hv : E.Valid hc z) : (resExpressionTorusTimes E n).2.Valid hc z := by
  induction n with
  | zero => exact hv
  | succ n ih => exact ⟨ih,nativeTorusSchema_valid z (E.setSchema_valid hc z hv).1⟩

theorem resExpressionTorusTimes_native_value (E : RESExpressionSchema B p sp a) (n : ℕ)
    (z : Fin p → M) (hv : E.Valid hc z) :
    (resExpressionTorusTimes E n).2.nativeValue hc z (resExpressionTorusTimes_valid E n z hv) =
      nativeTorusClass ⟨B.real ∪ Set.range z,B.gamma⟩ ^ n * E.nativeValue hc z hv := by
  induction n with
  | zero => exact (one_mul _).symm
  | succ n ih =>
    change (resExpressionTorusTimes E n).2.nativeValue hc z _ *
      nativeRESChartClass ((nativeTorusSchema B sp).chart hc z _) = _
    rw [ih,nativeTorusSchema_native_class z (E.setSchema_valid hc z hv).1,pow_succ]
    ring

theorem RESExpressionSchema.total_torus_step
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (E : RESExpressionSchema B p (fun _ => .rv) a)
    (hv : ∀ x : X, E.Valid hc (rvValues x.val)) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X (E.product (.atom (nativeTorusSchema B (fun _ => .rv)))).formalValue) =
    nativeTorusClass B * nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X E.formalValue) := by
  simp only [RESExpressionSchema.formalValue]
  rw [(relativeRESFormalEvaluator X).map_mul,E.relative_formal_evaluate X hv,relativeRESFormalEvaluator_atom]
  rw [nativeRelativeRVForget_class]
  exact nativeRelativeRVForget_value_product h00 linear hκ hs hr hγ hΓ kind X ⟨a,E.setSchema.domain⟩
    (GammaValueSchema.constant 1 (GammaGroupNames.one_definable_base B))
    (fun x => GammaValueSchema.constant_valid hc 1 (GammaGroupNames.one_definable_base B) _
      (fun i => (x.val i).property))

theorem resExpressionTorusTimes_total_formal_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (E : RESExpressionSchema B p (fun _ => .rv) a) (n : ℕ)
    (hv : ∀ x : X, E.Valid hc (rvValues x.val)) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X (resExpressionTorusTimes E n).2.formalValue) =
    nativeTorusClass B ^ n * nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X E.formalValue) := by
  induction n with
  | zero => exact (one_mul _).symm
  | succ n ih =>
    change nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X ((resExpressionTorusTimes E n).2.product
        (.atom (nativeTorusSchema B (fun _ => .rv)))).formalValue) = _
    rw [(resExpressionTorusTimes E n).2.total_torus_step h00 linear hκ hs hr hγ hΓ kind X
      (fun x => resExpressionTorusTimes_valid E n _ (hv x)),ih,pow_succ]
    ring

end DiamondIntegral.Section5
