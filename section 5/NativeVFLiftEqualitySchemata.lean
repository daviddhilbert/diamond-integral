import «section 5».NativeMixedBijectionPromotion
import «section 5».NativeFiniteRVLiftPresentations
import «section 5».NativeRVPresentedRowValues
import «section 5».NativeFiniteRVSchemaPromotion
import «section 5».RVEvaluationEqualityUniformity

/-! A whole original-language VF fibre witness contains both actual lift
graphs, both finite RV representative schemata, and the full stabilized
native RES equality. Its validity is a genuine first-order condition. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p n r m s : ℕ} {sp : Fin p → SortTag}

structure NativeVFLiftEqualitySchema (hc : CanonicalStructure.IsCanonical (M := M))
    (kind : EulerKind) (D : Set (Fin (p+(n+r)) → M)) (E : Set (Fin (p+(m+s)) → M)) where
  leftDegree : ℕ
  leftArity : ℕ
  leftRV : GammaFiniteRVSchema B p leftArity leftDegree sp
  rightDegree : ℕ
  rightArity : ℕ
  rightRV : GammaFiniteRVSchema B p rightArity rightDegree sp
  leftLift : GammaSortedBijectionChart B sp
    (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))
    (Fin.append (fun _ : Fin leftDegree => .vf) (fun _ : Fin leftArity => .rv))
  rightLift : GammaSortedBijectionChart B sp
    (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))
    (Fin.append (fun _ : Fin rightDegree => .vf) (fun _ : Fin rightArity => .rv))
  evaluation : RVEvaluationEqualitySchema hc kind (finiteRVSchemaDomain leftRV) (finiteRVSchemaDomain rightRV)

def NativeVFLiftEqualitySchema.Valid (hc : CanonicalStructure.IsCanonical (M := M))
    {kind : EulerKind} {D : Set (Fin (p+(n+r)) → M)} {E : Set (Fin (p+(m+s)) → M)}
    (W : NativeVFLiftEqualitySchema (B := B) (sp := sp) hc kind D E) (z : Fin p → M) : Prop :=
  nativeFiniteRVSchemaValid W.leftRV z ∧ nativeFiniteRVSchemaValid W.rightRV z ∧
    W.leftLift.valid D (finiteRVSchemaLiftDomain hc W.leftRV).val z ∧
      W.rightLift.valid E (finiteRVSchemaLiftDomain hc W.rightRV).val z ∧ W.evaluation.Valid hc z

theorem NativeVFLiftEqualitySchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {kind : EulerKind} {D : Set (Fin (p+(n+r)) → M)} {E : Set (Fin (p+(m+s)) → M)}
    (hD : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) D)
    (hE : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))) E)
    (W : NativeVFLiftEqualitySchema (B := B) (sp := sp) hc kind D E) :
    DefinableOverBase B sp {z | W.Valid hc z} :=
  (nativeFiniteRVSchemaValid_definable hc W.leftRV).inter
    ((nativeFiniteRVSchemaValid_definable hc W.rightRV).inter
      ((W.leftLift.valid_definable hD (finiteRVSchemaLiftDomain hc W.leftRV).property).inter
        ((W.rightLift.valid_definable hE (finiteRVSchemaLiftDomain hc W.rightRV).property).inter
          (W.evaluation.valid_definable hc))))

theorem native_vf_lift_equality_schema_at_parameter
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (D : Set (Fin (p+(n+r)) → M)) (E : Set (Fin (p+(m+s)) → M))
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (A : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawMixedSpace (M := M) n r))
    (C : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawMixedSpace (M := M) m s))
    (hA : {w | Fin.append z w ∈ D} = nativeMixedDomain A)
    (hC : {w | Fin.append z w ∈ E} = nativeMixedDomain C)
    {k l : ℕ}
    (U : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (V : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ l)
    (H : GammaGroundBijection A (gammaGroundObjectLift U))
    (K : GammaGroundBijection C (gammaGroundObjectLift V))
    (he : nativeRVEvaluation h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
      (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) kind
        (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U)) =
      nativeRVEvaluation h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
      (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) kind
        (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart V))) :
    ∃ W : NativeVFLiftEqualitySchema (B := B) (sp := sp) hc kind D E, W.Valid hc z := by
  obtain ⟨F,hF,hFd,hFv⟩ := native_finite_rv_schema_at_parameter hκ hs hr hγ z hz U
  obtain ⟨G,hG,hGd,hGv⟩ := native_finite_rv_schema_at_parameter hκ hs hr hγ z hz V
  obtain ⟨HP,hHP⟩ := native_mixed_fixed_bijection_chart_at_parameter z hz
    D (finiteRVSchemaLiftDomain hc F).val A (gammaGroundObjectLift U) hA
    (finiteRVSchemaLiftDomain_presents_native_lift z hz U F hFv) H
  obtain ⟨KP,hKP⟩ := native_mixed_fixed_bijection_chart_at_parameter z hz
    E (finiteRVSchemaLiftDomain hc G).val C (gammaGroundObjectLift V) hC
    (finiteRVSchemaLiftDomain_presents_native_lift z hz V G hGv) K
  have heRow : nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (finiteRVSchemaDomain F) z =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (finiteRVSchemaDomain G) z :=
    (native_rv_row_value_of_presentation h00 linear hκ hs hr hγ hΓ kind z U (finiteRVSchemaDomain F) hFd).trans
      (he.trans (native_rv_row_value_of_presentation h00 linear hκ hs hr hγ hΓ kind z V
        (finiteRVSchemaDomain G) hGd).symm)
  obtain ⟨W,hW⟩ := rv_evaluation_equality_schema_at_parameter h00 linear hκ hs hr hγ hΓ kind
    (finiteRVSchemaDomain F) (finiteRVSchemaDomain G) z hz heRow
  exact ⟨⟨k,U.arity,F,l,V.arity,G,HP,KP,W⟩,hF,hG,hHP,hKP,hW⟩

theorem native_vf_lift_equality_finite_catalog
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (kind : EulerKind) (X : Set (Fin p → M)) (hX : DefinableOverBase B sp X)
    (D : Set (Fin (p+(n+r)) → M)) (E : Set (Fin (p+(m+s)) → M))
    (hD : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) D)
    (hE : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))) E)
    (hrow : ∀ z ∈ X, ∃ W : NativeVFLiftEqualitySchema (B := B) (sp := sp) hc kind D E, W.Valid hc z) :
    ∃ J : Finset (NativeVFLiftEqualitySchema (B := B) (sp := sp) hc kind D E),
      ∀ z ∈ X, ∃ W ∈ J, W.Valid hc z :=
  gamma_finite_witnesses hκ hs hr hγ sp X hX
    (fun W : NativeVFLiftEqualitySchema (B := B) (sp := sp) hc kind D E => {z | W.Valid hc z})
    (fun W => W.valid_definable hc hD hE) hrow

end DiamondIntegral.Section5
