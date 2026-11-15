import «section 5».NativeGeometricVFLiftSchemata
import «section 5».NativeFiniteRVSchemaRecoding
import «section 5».RVEvaluationEqualityExtraPreparation

/-! One genuine preparation handles the geometric denominator witness,
both positive RV domains and full label graphs, and the base predicate.
The original VF lift graphs remain actual transported total bijections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p q n r m s : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def NativeGeometricVFLiftEqualitySchema.RVAgreement
    {D : Set (Fin (p+(n+r)) → M)} {E : Set (Fin (p+(m+s)) → M)}
    (W : NativeGeometricVFLiftEqualitySchema (B := B) (sp := sp) hc D E)
    (R : GammaParameterRecode B p q sp sq) (z : Fin p → M) (t : Fin q → M) : Prop :=
  W.evaluation.RowAgreement R z t ∧ R.DomainAgreement (finiteRVSchemaDomain W.leftRV) z t ∧
    R.DomainAgreement (finiteRVSchemaDomain W.rightRV) z t ∧
      R.RelationAgreement (finiteRVSchemaLabels W.leftRV) z t ∧
        R.RelationAgreement (finiteRVSchemaLabels W.rightRV) z t

theorem NativeGeometricVFLiftEqualitySchema.padded_values_descend
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {D : Set (Fin (p+(n+r)) → M)} {E : Set (Fin (p+(m+s)) → M)}
    (W : NativeGeometricVFLiftEqualitySchema (B := B) (sp := sp) hc D E)
    (R : GammaParameterRecode B p q sp sq) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i,sortEval (sp i) (z i)) (ht : ∀ i,sortEval (sq i) (t i))
    (hv : W.Valid z) (ha : W.RVAgreement R z t) :
    nativeFiniteRVSchemaValid (nativeFiniteRVSchemaRecode R W.leftRV) t ∧
      nativeFiniteRVSchemaValid (nativeFiniteRVSchemaRecode R W.rightRV) t ∧
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric
          (R.domain (originalPaddedRVDomain hc (finiteRVSchemaDomain W.leftRV) (W.commonDegree-W.leftDegree))) t =
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric
          (R.domain (originalPaddedRVDomain hc (finiteRVSchemaDomain W.rightRV) (W.commonDegree-W.rightDegree))) t := by
  refine ⟨(nativeFiniteRVSchemaValid_recode_iff R W.leftRV z t hz ht ha.2.1 ha.2.2.2.1).mp hv.1,
    (nativeFiniteRVSchemaValid_recode_iff R W.rightRV z t hz ht ha.2.2.1 ha.2.2.2.2).mp hv.2.1,?_⟩
  exact (W.evaluation.recode R).native_equality hc h00 linear hκ hs hr hγ hΓ t
    ((W.evaluation.recode_valid_iff R z t hz ht ha.1).mp hv.2.2.2.2)

theorem prepare_native_geometric_vf_lift_RV_data
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ)
    {S : Set M} {p q n r m s : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A))
    (D : Set (Fin ((p+q)+(n+r)) → M)) (E : Set (Fin ((p+q)+(m+s)) → M))
    (W : NativeGeometricVFLiftEqualitySchema (B := B)
      (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc D E)
    (Z : GammaDomainFormula B (p+q) 0 (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))) :
    ∃ R : Set M,∃ hSR : S ⊆ R,∃ hBR : B.real ⊆ R,
      ∃ l : ℕ,∃ C : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) C,
      ∃ hT : GammaChainDefinable B T.chain,IsRVPullback (carrier C) ∧
      ∀ (x : C) (v : Fin q → M),(∀ i,iRV (v i)) →
        W.RVAgreement (mixedPreparedParameterRecode T hT q)
          (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) ∧
        (mixedPreparedParameterRecode T hT q).DomainAgreement Z
          (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) := by
  let c : Option Bool → ℕ
    | none => 0
    | some false => W.leftArity
    | some true => W.rightArity
  let d : Bool → ℕ | false => W.leftArity | true => W.rightArity
  let e : Bool → ℕ | false => W.leftDegree | true => W.rightDegree
  let domain : (i : Option Bool) → GammaDomainFormula B (p+q) (c i)
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
    | none => Z
    | some false => finiteRVSchemaDomain W.leftRV
    | some true => finiteRVSchemaDomain W.rightRV
  let graph : (i : Bool) → GammaRelationFormula B (p+q) (d i) (e i)
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
    | false => finiteRVSchemaLabels W.leftRV
    | true => finiteRVSchemaLabels W.rightRV
  obtain ⟨R,hSR,hBR,l,C,T,hT,hC,hW,hD,hG⟩ := prepare_rv_equality_with_extra_data hc hκ hs h00 B hr A hA .geometric
    (originalPaddedRVDomain hc (finiteRVSchemaDomain W.leftRV) (W.commonDegree-W.leftDegree))
    (originalPaddedRVDomain hc (finiteRVSchemaDomain W.rightRV) (W.commonDegree-W.rightDegree)) {W.evaluation}
    c d e domain graph
  refine ⟨R,hSR,hBR,l,C,T,hT,hC,?_⟩
  intro x v hv
  exact ⟨⟨(hW W.evaluation (Finset.mem_singleton_self _) x v hv).1,
    hD (some false) x v,hD (some true) x v,hG false x v,hG true x v⟩,hD none x v⟩

end DiamondIntegral.Section5
