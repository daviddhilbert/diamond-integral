import «section 5».NativeGeometricWeightedRows
import «section 5».NativePreparedVFLiftValues
import «section 5».GeometricWeightedRVFubini

/-! Actual prepared RV keys carry the full intrinsic geometric weighted
row equality. Every original-ground subbase, including a VF zero stratum,
therefore has equal common-degree normalized total values. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {p l q : ℕ}

theorem nativePreparedGeometricVFLift_row_values
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {n r m s : ℕ} {D : Set (Fin ((p+q)+(n+r)) → M)} {E : Set (Fin ((p+q)+(m+s)) → M)}
    (W : NativeGeometricVFLiftEqualitySchema (B := B)
      (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc D E)
    (Z : GammaDomainFormula B (p+q) 0 (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (hW : ∀ z,Fin.append z (Fin.elim0 : Fin 0 → M) ∈ Z.val → W.Valid z)
    {A : DefSet (M := M) S p 0} {C : DefSet (M := M) S p l}
    (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain)
    (hprep : ∀ (x : C) (v : Fin q → M),(∀ i,iRV (v i)) →
      W.RVAgreement (mixedPreparedParameterRecode T hT q)
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) ∧
      (mixedPreparedParameterRecode T hT q).DomainAgreement Z
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v))
    (t : Fin ((p+l)+q) → M)
    (ht : t ∈ rawDomain (nativePreparedParameterBase (hc := hc) C
      (GammaChainDefinable.target B T.chain hT) ((mixedPreparedParameterRecode T hT q).domain Z))) :
    nativeFiniteRVSchemaValid (nativeFiniteRVSchemaRecode (mixedPreparedParameterRecode T hT q) W.leftRV) t ∧
      nativeFiniteRVSchemaValid (nativeFiniteRVSchemaRecode (mixedPreparedParameterRecode T hT q) W.rightRV) t ∧
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric
            ((mixedPreparedParameterRecode T hT q).domain (finiteRVSchemaDomain W.leftRV)) t *
          RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range t,B.gamma⟩ : Base (M := M)) ^
            (W.commonDegree-W.leftDegree) =
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric
            ((mixedPreparedParameterRecode T hT q).domain (finiteRVSchemaDomain W.rightRV)) t *
          RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range t,B.gamma⟩ : Base (M := M)) ^
            (W.commonDegree-W.rightDegree) := by
  obtain ⟨x,v,hv,he,hz⟩ := nativePreparedParameterBase_representative C
    (GammaChainDefinable.target B T.chain hT) ((mixedPreparedParameterRecode T hT q).domain Z) t ht
  rw [←he] at hz ⊢
  have hrow := hprep x v hv
  have hvalid := hW (Fin.append (rawVFParameter (T.inverseMap x).val) v)
    ((hrow.2 (Fin.elim0 : Fin 0 → M)).mpr hz)
  apply W.weighted_values_descend h00 linear hκ hs hr hγ hΓ (mixedPreparedParameterRecode T hT q)
    (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) ?_ ?_ hvalid hrow.1
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left,rawVFParameter] using ((T.inverseMap x).val.1 j).property
    · simpa only [Fin.append_right,sortEval,iRV] using hv j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left,rawPreparedKey,sortEval,iRV] using ((flatKey x.val).2 j).property
    · simpa only [Fin.append_right,sortEval,iRV] using hv j

theorem nativePreparedGeometricVFLift_subbase_total_values
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {n r m s : ℕ} {D : Set (Fin ((p+q)+(n+r)) → M)} {E : Set (Fin ((p+q)+(m+s)) → M)}
    (W : NativeGeometricVFLiftEqualitySchema (B := B)
      (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc D E)
    (Z : GammaDomainFormula B (p+q) 0 (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (hW : ∀ z,Fin.append z (Fin.elim0 : Fin 0 → M) ∈ Z.val → W.Valid z)
    {A : DefSet (M := M) S p 0} {C : DefSet (M := M) S p l}
    (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain)
    (hprep : ∀ (x : C) (v : Fin q → M),(∀ i,iRV (v i)) →
      W.RVAgreement (mixedPreparedParameterRecode T hT q)
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) ∧
      (mixedPreparedParameterRecode T hT q).DomainAgreement Z
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v))
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) ((p+l)+q)))
    (hX : X.carrier ⊆ (nativePreparedParameterBase (hc := hc) C (GammaChainDefinable.target B T.chain hT)
      ((mixedPreparedParameterRecode T hT q).domain Z)).carrier) (d : ℕ) :
    geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine B)
        (nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ .geometric
          (originalRVTotalFamily X ((mixedPreparedParameterRecode T hT q).domain (finiteRVSchemaDomain W.leftRV))))
        (d+W.leftDegree) =
      geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine B)
        (nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ .geometric
          (originalRVTotalFamily X ((mixedPreparedParameterRecode T hT q).domain (finiteRVSchemaDomain W.rightRV))))
        (d+W.rightDegree) := by
  apply native_geometric_rv_family_common_degree h00 linear hκ hs hr hγ hΓ X _ _ d W.leftDegree W.rightDegree
    (W.commonDegree-W.leftDegree) (W.commonDegree-W.rightDegree) ?_ ?_
  · rw [Nat.add_sub_of_le W.left_le,Nat.add_sub_of_le W.right_le]
  · rintro z ⟨x,hx,he⟩
    exact (nativePreparedGeometricVFLift_row_values h00 linear hκ hs hr hγ hΓ W Z hW T hT hprep
      z ⟨x,hX hx,he⟩).2.2

end DiamondIntegral.Section5
