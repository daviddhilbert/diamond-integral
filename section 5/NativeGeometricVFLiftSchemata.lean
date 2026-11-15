import «section 5».NativeVFLiftEqualitySchemata
import «section 5».GeometricPaddedRVRows
import «section 5».NativeGeometricRetraction

/-! Complete first-order geometric VF fibre witnesses retain the original
positive lift graphs and a finite common denominator degree. The RES
certificate compares literal affine-padded RV domains over the original
parameters. No bound on the padding degree is assumed before compactness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
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
variable {p n r m s : ℕ} {sp : Fin p → SortTag}

structure NativeGeometricVFLiftEqualitySchema (hc : CanonicalStructure.IsCanonical (M := M))
    (D : Set (Fin (p+(n+r)) → M)) (E : Set (Fin (p+(m+s)) → M)) where
  leftDegree : ℕ
  leftArity : ℕ
  leftRV : GammaFiniteRVSchema B p leftArity leftDegree sp
  rightDegree : ℕ
  rightArity : ℕ
  rightRV : GammaFiniteRVSchema B p rightArity rightDegree sp
  commonDegree : ℕ
  left_le : leftDegree ≤ commonDegree
  right_le : rightDegree ≤ commonDegree
  leftLift : GammaSortedBijectionChart B sp
    (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))
    (Fin.append (fun _ : Fin leftDegree => .vf) (fun _ : Fin leftArity => .rv))
  rightLift : GammaSortedBijectionChart B sp
    (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))
    (Fin.append (fun _ : Fin rightDegree => .vf) (fun _ : Fin rightArity => .rv))
  evaluation : RVEvaluationEqualitySchema hc .geometric
    (originalPaddedRVDomain hc (finiteRVSchemaDomain leftRV) (commonDegree-leftDegree))
    (originalPaddedRVDomain hc (finiteRVSchemaDomain rightRV) (commonDegree-rightDegree))

def NativeGeometricVFLiftEqualitySchema.Valid
    {D : Set (Fin (p+(n+r)) → M)} {E : Set (Fin (p+(m+s)) → M)}
    (W : NativeGeometricVFLiftEqualitySchema (B := B) (sp := sp) hc D E) (z : Fin p → M) : Prop :=
  nativeFiniteRVSchemaValid W.leftRV z ∧ nativeFiniteRVSchemaValid W.rightRV z ∧
    W.leftLift.valid D (finiteRVSchemaLiftDomain hc W.leftRV).val z ∧
      W.rightLift.valid E (finiteRVSchemaLiftDomain hc W.rightRV).val z ∧ W.evaluation.Valid hc z

theorem NativeGeometricVFLiftEqualitySchema.valid_definable
    {D : Set (Fin (p+(n+r)) → M)} {E : Set (Fin (p+(m+s)) → M)}
    (hD : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) D)
    (hE : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))) E)
    (W : NativeGeometricVFLiftEqualitySchema (B := B) (sp := sp) hc D E) :
    DefinableOverBase B sp {z | W.Valid z} :=
  (nativeFiniteRVSchemaValid_definable hc W.leftRV).inter
    ((nativeFiniteRVSchemaValid_definable hc W.rightRV).inter
      ((W.leftLift.valid_definable hD (finiteRVSchemaLiftDomain hc W.leftRV).property).inter
        ((W.rightLift.valid_definable hE (finiteRVSchemaLiftDomain hc W.rightRV).property).inter
          (W.evaluation.valid_definable hc))))

theorem native_geometric_vf_lift_schema_at_parameter
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (D : Set (Fin (p+(n+r)) → M)) (E : Set (Fin (p+(m+s)) → M))
    (z : Fin p → M) (hz : ∀ i,sortEval (sp i) (z i))
    (A : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawMixedSpace (M := M) n r))
    (C : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawMixedSpace (M := M) m s))
    (hA : {w | Fin.append z w ∈ D} = nativeMixedDomain A)
    (hC : {w | Fin.append z w ∈ E} = nativeMixedDomain C)
    {k l : ℕ} (U : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (V : GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ l)
    (H : GammaGroundBijection A (gammaGroundObjectLift U))
    (K : GammaGroundBijection C (gammaGroundObjectLift V))
    (he : nativeGeometricRetraction h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl)
        (RVOrdinaryPNormalization.quotient _ (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U))) =
      nativeGeometricRetraction h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl)
        (RVOrdinaryPNormalization.quotient _ (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart V)))) :
    ∃ W : NativeGeometricVFLiftEqualitySchema (B := B) (sp := sp) hc D E,W.Valid z := by
  obtain ⟨F,hF,hFd,hFv⟩ := native_finite_rv_schema_at_parameter hκ hs hr hγ z hz U
  obtain ⟨G,hG,hGd,hGv⟩ := native_finite_rv_schema_at_parameter hκ hs hr hγ z hz V
  obtain ⟨HP,hHP⟩ := native_mixed_fixed_bijection_chart_at_parameter z hz
    D (finiteRVSchemaLiftDomain hc F).val A (gammaGroundObjectLift U) hA
    (finiteRVSchemaLiftDomain_presents_native_lift z hz U F hFv) H
  obtain ⟨KP,hKP⟩ := native_mixed_fixed_bijection_chart_at_parameter z hz
    E (finiteRVSchemaLiftDomain hc G).val C (gammaGroundObjectLift V) hC
    (finiteRVSchemaLiftDomain_presents_native_lift z hz V G hGv) K
  have hUF := native_rv_row_value_of_presentation h00 linear hκ hs hr hγ hΓ .geometric z U (finiteRVSchemaDomain F) hFd
  have hVG := native_rv_row_value_of_presentation h00 linear hκ hs hr hγ hΓ .geometric z V (finiteRVSchemaDomain G) hGd
  rw [nativeGeometricRetraction_class,nativeGeometricRetraction_class,←hUF,←hVG] at he
  obtain ⟨N,hk,hl,hePad⟩ := (geometricRowValue_eq_iff_padded h00 linear hκ hs hr hγ hΓ
    (finiteRVSchemaDomain F) (finiteRVSchemaDomain G) k l z hz).mp he
  obtain ⟨W,hW⟩ := rv_evaluation_equality_schema_at_parameter h00 linear hκ hs hr hγ hΓ .geometric
    (originalPaddedRVDomain hc (finiteRVSchemaDomain F) (N-k))
    (originalPaddedRVDomain hc (finiteRVSchemaDomain G) (N-l)) z hz hePad
  exact ⟨⟨k,U.arity,F,l,V.arity,G,N,hk,hl,HP,KP,W⟩,hF,hG,hHP,hKP,hW⟩

theorem native_geometric_vf_lift_finite_catalog
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (X : Set (Fin p → M)) (hX : DefinableOverBase B sp X)
    (D : Set (Fin (p+(n+r)) → M)) (E : Set (Fin (p+(m+s)) → M))
    (hD : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) D)
    (hE : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))) E)
    (hrow : ∀ z ∈ X,∃ W : NativeGeometricVFLiftEqualitySchema (B := B) (sp := sp) hc D E,W.Valid z) :
    ∃ J : Finset (NativeGeometricVFLiftEqualitySchema (B := B) (sp := sp) hc D E),
      ∀ z ∈ X,∃ W ∈ J,W.Valid z :=
  gamma_finite_witnesses hκ hs hr hγ sp X hX
    (fun W : NativeGeometricVFLiftEqualitySchema (B := B) (sp := sp) hc D E => {z | W.Valid z})
    (fun W => W.valid_definable hD hE) hrow

end DiamondIntegral.Section5
