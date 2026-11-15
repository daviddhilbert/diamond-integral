import «section 5».RESLayoutUniformity
import «section 5».RESLayoutPreparation

/-! Native RES equality descends through one genuine preparation by its
whole finite witness catalog, including all graphs and coefficient domains. -/
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

theorem native_res_equality_descends (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {S : Set M} {p q a b : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A))
    (Z : Set (Fin (p+q) → M))
    (hZ : DefinableOverBase B (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) Z)
    (F : RESSetSchema B (p+q) a (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (G : RESSetSchema B (p+q) b (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (hF : ∀ z ∈ Z, F.Valid hc z) (hG : ∀ z ∈ Z, G.Valid hc z)
    (he : ∀ z, ∀ hz : z ∈ Z,
      nativeRESChartClass (F.chart hc z (hF z hz)) = nativeRESChartClass (G.chart hc z (hG z hz))) :
    ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ hBR : B.real ⊆ R,
      ∃ l : ℕ, ∃ C : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) C,
      ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier C) ∧
      ∀ (x : C) (v : Fin q → M), (∀ i, iRV (v i)) →
        Fin.append (rawVFParameter (T.inverseMap x).val) v ∈ Z →
        ∃ (hf : (F.recode (mixedPreparedParameterRecode T hT q)).Valid hc (Fin.append (rawPreparedKey x.val) v))
          (hg : (G.recode (mixedPreparedParameterRecode T hT q)).Valid hc (Fin.append (rawPreparedKey x.val) v)),
          nativeRESChartClass ((F.recode (mixedPreparedParameterRecode T hT q)).chart hc
            (Fin.append (rawPreparedKey x.val) v) hf) =
          nativeRESChartClass ((G.recode (mixedPreparedParameterRecode T hT q)).chart hc
            (Fin.append (rawPreparedKey x.val) v) hg) := by
  obtain ⟨J, hJ⟩ := res_equality_finite_layout_catalog hκ.le hs B hr hγ _ Z hZ F G hF hG he
  obtain ⟨R, hSR, hBR, l, C, T, hT, hC, hprep⟩ :=
    prepare_finite_res_layout_catalog hc hκ hs h00 B hr A hA F G J
  refine ⟨R, hSR, hBR, l, C, T, hT, hC, ?_⟩
  intro x v hv hz
  obtain ⟨W, hW, hvalid⟩ := hJ _ hz
  have hnew := ((hprep W hW x v hv).2).mp hvalid
  exact ⟨hnew.1, hnew.2.1, (W.recode _).native_equality hc _ hnew⟩

end DiamondIntegral.Section5
