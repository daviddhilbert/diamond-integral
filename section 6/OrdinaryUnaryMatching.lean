import «section 6».OrdinaryGammaGraphs

/-! The cited ordinary simultaneous unary matching theorem, applied to
the actual original-base raw sets and full bijection graph. Internal real
codes do not replace its original-base primitive graph certificates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_ordinary_unary_matching
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hnt : ∃ x : B₀.field,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (B : DefSet (rawMixedSpace (M := M) 1 s) (S : Set M))
    (f : Map A B) (hf : Function.Bijective f) :
    ∃ R : Set M, ∃ hSR : (S : Set M) ⊆ R,
      ∃ a b : ℕ, ∃ A' : SpecialTransformations.Section5.DefSet (M := M) R 1 a,
      ∃ B' : SpecialTransformations.Section5.DefSet (M := M) R 1 b,
      ∃ TA : SpecialTransformations.Section5.SpecialBijection
        (SpecialTransformations.Section5.extendBase (toOrdinarySet hc A) hSR) A',
      ∃ TB : SpecialTransformations.Section5.SpecialBijection
        (SpecialTransformations.Section5.extendBase (toOrdinarySet hc B) hSR) B',
        SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase (S : Set M)) TA.chain ∧
        SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase (S : Set M)) TB.chain ∧
        SpecialTransformations.Section5.IsRVPullback (SpecialTransformations.Section5.carrier A') ∧
        SpecialTransformations.Section5.IsRVPullback (SpecialTransformations.Section5.carrier B') ∧
        let fR := @SpecialTransformations.DefinableGeometry.Map.extend LRV M
          (CanonicalStructure.normalize (M := M)) _ _ (S : Set M) R _ _ (toOrdinaryMap hc f) hSR
        SpecialTransformations.Section5.Contractible (IntegrationInACVF.Section5.unaryConjugate TA TB fR) ∧
        SpecialTransformations.Section5.Contractible
          (SpecialTransformations.Section5.Map.inverse (IntegrationInACVF.Section5.unaryConjugate TA TB fR)
            (IntegrationInACVF.Section5.unaryConjugate_bijective TA TB fR hf)) ∧
        SpecialTransformations.Section5.GammaGraphDefinable (ordinaryNamedGammaBase (S : Set M))
          (SpecialTransformations.Section5.pointMapGraph (IntegrationInACVF.Section5.unaryConjugate TA TB fR)) := by
  obtain ⟨hV,hVS,hSV,hnt'⟩ := vfGenerated_base_support S B₀ hnt
  obtain ⟨c,hc0,hcDef,hcVal⟩ := exists_named_vf_above_radius Valued.v hv hc h00
    (vfFieldNames B₀.field) (S : Set M) hV hVS hSV hnt' 1 le_rfl (gamma_one_named hc)
  let δ := finiteValue c hc0
  have hδ : δ ∈ (ordinaryNamedGammaBase (S : Set M)).gamma := finiteValue_named c hc0 hcDef
  have hδ1 : 1 < δ := hcVal
  let P := ordinaryNamedGammaBase (S : Set M)
  have hA := (SpecialTransformations.Section5.gammaLogicInput P).real_set _
    (SpecialTransformations.Section5.setDefinable (toOrdinarySet hc A))
  have hB := (SpecialTransformations.Section5.gammaLogicInput P).real_set _
    (SpecialTransformations.Section5.setDefinable (toOrdinarySet hc B))
  have hF := (SpecialTransformations.Section5.gammaLogicInput P).real_map_graph (toOrdinaryMap hc f)
  obtain ⟨R,hSR,a,b,A',B',TA,TB,hTA,hTB,hA',hB',hForward,hReverse,hGraph,hKeys⟩ :=
    IntegrationInACVF.Section5.lemma_5_2_gamma_presented (P := P) hκ.le hs hsmall h00 δ hδ hδ1
      B₀.toVFFieldBase (fun _ h => h) (toOrdinaryMap hc f) hf hA hB hF
  exact ⟨R,hSR,a,b,A',B',TA,TB,hTA,hTB,hA',hB',hForward,hReverse,hGraph⟩

end DiamondIntegral.Section6
