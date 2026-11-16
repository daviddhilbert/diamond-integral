import «section 6».FocusComponentTemplateRealizations
import «section 6».CanonicalPointwiseProtection
import «section 6».TemplateValueIdentities

/-! Every actual synchronized component on a pullback fibre promotes
to an original-base admissible component template. All old RV labels,
the exact coefficient and the complete focus family are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_promoted_focus_component_template
    (h00 : M ⊨ Axioms.ACVF00) (hcModel : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (hsmall : Cardinal.mk ↥(S ∪ Set.range a) < κ)
    (hΓ : NontrivialDefinableGamma (⟨S ∪ Set.range a,∅⟩ : ParameterBase M))
    (D : CentripetalData (G := G) (A.fibre a)) (hARV : IsRVPullback (A.fibre a).carrier)
    (E : ∀ i,CentripetalData (G := G) ((P i).fibre a))
    (hCompat : ∀ i,ApertureRestrictionData D (E i)) :
    ∃ T : FocusComponentParameterTemplate (M := M) S p n r,∃ ha : a ∈ T.good A P,
      T.coordinate=D.coordinate ∧ T.active.fibre a=D.activeTags ∧
        vfScalarTemplateValue T.coefficient a ha.1.1.2=D.coefficient ∧
          ∀ u x,T.focus.value a ha.1.1.1 u x=totalFocusFibre D.focusMap u x := by
  obtain ⟨W,hCoeff,hPoint,hMove⟩ := D.exists_pointwise_protected_source_data
    h00 hcModel linear hκ hs hv hsmall hΓ hARV (fun i => (P i).fibre a) E hCompat
  obtain ⟨hCont,hFamily⟩ := proper_partial_focus_total_rv_family_graph hv D.focusMap
    (focusActive_properInvariant (A.fibre a) D.sourceProper D.activeTags) D.focusMap_continuous
  obtain ⟨F,hF,hFSection⟩ := exists_promoted_continuous_rv_graph_template hv a
    (totalFocusFibre D.focusMap) hFamily hCont
  obtain ⟨U,hU,hUSection⟩ := exists_promoted_rv_set_template a D.activeTags
  obtain ⟨C,hC,hCValue⟩ := exists_promoted_vf_scalar_name_template hv a W.coefficient W.coefficient_named
  obtain ⟨B,hB,hBSection⟩ := exists_promoted_gamma_name_template a W.radius W.radius_named
  have hBValue := B.value_of_name a hB W.radius hBSection
  let T : FocusComponentParameterTemplate (M := M) S p n r := ⟨D.coordinate,U,F,C,B⟩
  let f := F.value a hF
  have hf := F.family_graph_definable a hF
  let fA := rvFamilyMap (focusActive (A.fibre a) (U.fibre a)) f hf
  have hFocusValue {Q : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
      (hQA : Q.carrier ⊆ (A.fibre a).carrier) (x : focusActive Q (U.fibre a)) :
      F.value a hF x.val.2 x.val.1=
        (D.focusMap ⟨x.val,hQA x.property.1,by simpa only [hU] using x.property.2⟩).val := by
    rw [F.value_eq_of_graph a hF (totalFocusFibre D.focusMap) hFSection x.val.2 x.val.1]
    exact totalFocusFibre_at D.focusMap x.val.2 x.val.1
      ⟨hQA x.property.1,by simpa only [hU] using x.property.2⟩
  have hValueA (x : focusActive (A.fibre a) (U.fibre a)) :
      (fA x).val 0=(D.focusMap ⟨x.val,x.property.1,by simpa only [hU] using x.property.2⟩).val 0 :=
    congrFun (hFocusValue (fun _ hx => hx) x) 0
  have hGraph := focusGraphParameterCode_at A U F a hF
  have hAcode := (A.fibre_code a).symm
  have hTagged : a ∈ taggedSourceParameterLocus A.typedGraph :=
    (mem_taggedSourceParameterLocus_iff A.typedGraph a (A.fibre a) hAcode).mpr D.tagged
  have hIndependent : a ∈ focusIndependentParameterLocus (focusGraphParameterCode A U F) D.coordinate := by
    apply (mem_focusIndependentParameterLocus_map_iff _ a D.coordinate fA hGraph).mpr
    intro x y hu ho
    rw [hValueA x,hValueA y]
    exact D.fullFocusGraph.independent _ _ hu ho
  have hLeading : a ∈ focusLeadingTermParameterLocus (focusGraphParameterCode A U F) D.coordinate := by
    apply (mem_focusLeadingTermParameterLocus_map_iff _ a D.coordinate fA hGraph).mpr
    intro x
    rw [hValueA x]
    exact D.fullFocusGraph.leadingTerm _
  have hMeta : a ∈ focusMetadataParameterLocus C B (T.geometricLocus A P) := by
    intro c b hc hb
    have hc0 := (vfScalarTemplateValue_of_entry C a hC c hc).trans (congrArg Subtype.val hCValue)
    have hcCode : c=(fun _ : Fin 1 => W.coefficient.val) := by funext i; fin_cases i; exact hc0
    let t : RVInfinity M := ⟨b 0,(B.proper _ hb).1⟩
    have ht : t ≠ rvZero M := fun h => (B.proper _ hb).2 (congrArg Subtype.val h)
    have hGamma : GammaParameters.codeValue t.val=W.radius := (B.value_of_entry a hB b hb).trans hBValue
    have hbCode : b=(fun _ : Fin 1 => t.val) := by funext i; fin_cases i; rfl
    rw [hcCode,hbCode]
    refine ⟨⟨(coefficientCodeCondition_at a W.coefficient t).mpr ⟨W.nonzero,W.nonnegative⟩,⟨?_,?_⟩⟩,?_⟩
    · apply (mem_focusSourceInvariantParameterLocus_map_iff A.typedGraph
        (focusGraphParameterCode A U F) a W.coefficient t ht D.coordinate fA hAcode hGraph).mpr
      intro x y hab
      rw [hGamma,hValueA x] at hab
      exact W.source ⟨x.val,x.property.1,by
        change x.val.2 ∈ D.activeTags.carrier
        simpa only [hU] using x.property.2⟩ y hab
    · apply (mem_focusErasedCovarianceParameterLocus_map_iff
        (focusGraphParameterCode A U F) a W.coefficient t ht D.coordinate fA hGraph).mpr
      intro x y hu hab
      rw [hGamma] at hab
      rw [hValueA x,hValueA y]
      exact W.focus _ _ hu hab
    · apply Set.mem_iInter.mpr
      intro i
      let fP := rvFamilyMap (focusActive ((P i).fibre a) (U.fibre a)) f hf
      have hPGraph := focusGraphParameterCode_at (P i) U F a hF
      have hValueP (x : focusActive ((P i).fibre a) (U.fibre a)) :
          (fP x).val 0=(D.focusMap ⟨x.val,(hCompat i).subset x.property.1,
            by simpa only [hU] using x.property.2⟩).val 0 := congrFun (hFocusValue (hCompat i).subset x) 0
      apply (mem_focusSourceInvariantParameterLocus_map_iff (P i).typedGraph
        (focusGraphParameterCode (P i) U F) a W.coefficient t ht D.coordinate fP
          ((P i).fibre_code a).symm hPGraph).mpr
      intro x y hab
      rw [hGamma,hValueP x] at hab
      exact hMove i ⟨x.val,x.property.1,by simpa only [hU] using x.property.2⟩ y hab
  have ha : a ∈ T.good A P := ⟨⟨⟨hF,hC⟩,hB⟩,⟨⟨⟨hTagged,hIndependent⟩,hLeading⟩,hMeta⟩⟩
  exact ⟨T,ha,rfl,hU,hCValue.trans hCoeff,fun u x =>
    F.value_eq_of_graph a hF (totalFocusFibre D.focusMap) hFSection u x⟩

end DiamondIntegral.Section6
