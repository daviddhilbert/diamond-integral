import «section 5».RVEvaluationEqualityUniformity
import «section 5».RVEvaluationEqualityPreparation

/-! Actual equality of native RV fibre values descends from mixed VF/RV
parameters to one prepared RV key by transporting full finite witnesses.
No injectivity of a change-of-parameter-base map is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem native_rv_equality_descends (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    {S : Set M} {p q a b : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A))
    (Z : Set (Fin (p+q) → M))
    (hZ : DefinableOverBase B (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) Z)
    (D : GammaDomainFormula B (p+q) a (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (E : GammaDomainFormula B (p+q) b (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (he : ∀ z ∈ Z, nativeRVRowValue (hc := hc) h00 linear hκ.le hs hr hγ hΓ kind D z =
      nativeRVRowValue (hc := hc) h00 linear hκ.le hs hr hγ hΓ kind E z) :
    ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ hBR : B.real ⊆ R,
      ∃ l : ℕ, ∃ C : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) C,
      ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier C) ∧
      ∀ (x : C) (v : Fin q → M), (∀ i, iRV (v i)) →
        Fin.append (rawVFParameter (T.inverseMap x).val) v ∈ Z →
        nativeRVRowValue (hc := hc) h00 linear hκ.le hs hr hγ hΓ kind
          ((mixedPreparedParameterRecode T hT q).domain D) (Fin.append (rawPreparedKey x.val) v) =
        nativeRVRowValue (hc := hc) h00 linear hκ.le hs hr hγ hΓ kind
          ((mixedPreparedParameterRecode T hT q).domain E) (Fin.append (rawPreparedKey x.val) v) := by
  obtain ⟨J,hJ⟩ := rv_equality_finite_package_catalog h00 linear hκ.le hs hr hγ hΓ kind Z hZ D E he
  obtain ⟨R,hSR,hBR,l,C,T,hT,hC,hprep⟩ :=
    prepare_rv_evaluation_equality_catalog hc hκ hs h00 B hr A hA kind D E J
  refine ⟨R,hSR,hBR,l,C,T,hT,hC,?_⟩
  intro x v hv hz
  obtain ⟨W,hW,hvalid⟩ := hJ _ hz
  have hnew := (hprep W hW x v hv).2.mp hvalid
  exact (W.recode (mixedPreparedParameterRecode T hT q)).native_equality hc h00 linear hκ.le hs hr hγ hΓ _ hnew

end DiamondIntegral.Section5
