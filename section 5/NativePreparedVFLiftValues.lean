import «section 5».NativePreparedKeyDomains
import «section 5».NativeVFLiftRVPreparation
import «section 5».NativeRVFamilyFubini

/-! The original-ground prepared RV base carries genuine finite nonzero
representatives and actual native row equalities. RV-family Fubini then
compares their literal totals over the original ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
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

theorem nativePreparedParameterBase_representative (C : DefSet (M := M) S p l)
    (hC : GammaSetDefinable B (carrier C))
    (Z : GammaDomainFormula B ((p+l)+q) 0 (fun _ => .rv))
    (t : Fin ((p+l)+q) → M) (ht : t ∈ rawDomain (nativePreparedParameterBase (hc := hc) C hC Z)) :
    ∃ c : C, ∃ v : Fin q → M, (∀ i,iRV (v i)) ∧ Fin.append (rawPreparedKey c.val) v = t ∧
      Fin.append t (Fin.elim0 : Fin 0 → M) ∈ Z.val := by
  have hp := (rawDomain_definable (nativePreparedParameterBase (hc := hc) C hC Z)).proper t ht
  rw [nativePreparedParameterBase_raw] at ht
  obtain ⟨hz,c,hc⟩ := ht
  refine ⟨c,t ∘ Fin.natAdd (p+l),(fun i => hp (Fin.natAdd (p+l) i)),?_,hz⟩
  rw [hc]
  exact Fin.append_castAdd_natAdd

theorem nativePreparedVFLift_row_values
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    {n r m s : ℕ}
    {D : Set (Fin ((p+q)+(n+r)) → M)} {E : Set (Fin ((p+q)+(m+s)) → M)}
    (W : NativeVFLiftEqualitySchema (B := B)
      (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc kind D E)
    (Z : GammaDomainFormula B (p+q) 0 (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (hW : ∀ z, Fin.append z (Fin.elim0 : Fin 0 → M) ∈ Z.val → W.Valid hc z)
    {A : DefSet (M := M) S p 0} {C : DefSet (M := M) S p l}
    (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain)
    (hprep : ∀ (x : C) (v : Fin q → M), (∀ i,iRV (v i)) →
      W.RVAgreement (mixedPreparedParameterRecode T hT q)
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) ∧
      (mixedPreparedParameterRecode T hT q).DomainAgreement Z
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v))
    (t : Fin ((p+l)+q) → M)
    (ht : t ∈ rawDomain (nativePreparedParameterBase (hc := hc) C
      (GammaChainDefinable.target B T.chain hT) ((mixedPreparedParameterRecode T hT q).domain Z))) :
    nativeFiniteRVSchemaValid (nativeFiniteRVSchemaRecode (mixedPreparedParameterRecode T hT q) W.leftRV) t ∧
      nativeFiniteRVSchemaValid (nativeFiniteRVSchemaRecode (mixedPreparedParameterRecode T hT q) W.rightRV) t ∧
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind
          ((mixedPreparedParameterRecode T hT q).domain (finiteRVSchemaDomain W.leftRV)) t =
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind
          ((mixedPreparedParameterRecode T hT q).domain (finiteRVSchemaDomain W.rightRV)) t := by
  obtain ⟨x,v,hv,he,hz⟩ := nativePreparedParameterBase_representative C
    (GammaChainDefinable.target B T.chain hT) ((mixedPreparedParameterRecode T hT q).domain Z) t ht
  rw [←he] at hz ⊢
  have hrow := hprep x v hv
  have hvalid := hW (Fin.append (rawVFParameter (T.inverseMap x).val) v)
    ((hrow.2 (Fin.elim0 : Fin 0 → M)).mpr hz)
  apply W.rv_values_descend h00 linear hκ hs hr hγ hΓ (mixedPreparedParameterRecode T hT q)
    (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) ?_ ?_ hvalid hrow.1
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left,rawVFParameter] using ((T.inverseMap x).val.1 j).property
    · simpa only [Fin.append_right,sortEval,iRV] using hv j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left,rawPreparedKey,sortEval,iRV] using ((flatKey x.val).2 j).property
    · simpa only [Fin.append_right,sortEval,iRV] using hv j

theorem nativePreparedVFLift_total_values
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    {n r m s : ℕ}
    {D : Set (Fin ((p+q)+(n+r)) → M)} {E : Set (Fin ((p+q)+(m+s)) → M)}
    (W : NativeVFLiftEqualitySchema (B := B)
      (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc kind D E)
    (Z : GammaDomainFormula B (p+q) 0 (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (hW : ∀ z, Fin.append z (Fin.elim0 : Fin 0 → M) ∈ Z.val → W.Valid hc z)
    {A : DefSet (M := M) S p 0} {C : DefSet (M := M) S p l}
    (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain)
    (hprep : ∀ (x : C) (v : Fin q → M), (∀ i,iRV (v i)) →
      W.RVAgreement (mixedPreparedParameterRecode T hT q)
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) ∧
      (mixedPreparedParameterRecode T hT q).DomainAgreement Z
        (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v)) :
    let X := nativePreparedParameterBase (hc := hc) C (GammaChainDefinable.target B T.chain hT)
      ((mixedPreparedParameterRecode T hT q).domain Z)
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
        (originalRVTotalFamily X ((mixedPreparedParameterRecode T hT q).domain (finiteRVSchemaDomain W.leftRV))) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
        (originalRVTotalFamily X ((mixedPreparedParameterRecode T hT q).domain (finiteRVSchemaDomain W.rightRV))) := by
  dsimp only
  apply native_rv_family_fubini h00 linear hκ hs hr hγ hΓ kind
  intro x
  exact (nativePreparedVFLift_row_values h00 linear hκ hs hr hγ hΓ kind W Z hW T hT hprep
    (rvValues x.val) ⟨x.val,x.property,rfl⟩).2.2

end DiamondIntegral.Section5
