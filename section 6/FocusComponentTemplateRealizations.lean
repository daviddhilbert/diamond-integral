import «section 6».FocusComponentParameterTemplates

/-! Admissibility of a complete component template reconstructs its
actual permitted component and every protected restriction, over exactly
the original base and the given real parameter tuple. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem FocusComponentParameterTemplate.exists_component
    (hcModel : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (a : Fin p → M) (ha : a ∈ T.good A P)
    (hA : ProperInvariant (S ∪ Set.range a) (A.fibre a).carrier)
    (hAD : VFDoublyBounded (A.fibre a).carrier)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier)
    (hP : ∀ i,ProperInvariant (S ∪ Set.range a) ((P i).fibre a).carrier) :
    ∃ D : CentripetalData (G := G) (A.fibre a),D.coordinate=T.coordinate ∧
      D.activeTags=T.active.fibre a ∧ D.coefficient=vfScalarTemplateValue T.coefficient a ha.1.1.2 ∧
      (∀ q : focusActive (A.fibre a) (T.active.fibre a),D.extendedFocus q.val=
        T.focus.value a ha.1.1.1 q.val.2 q.val.1 0) ∧
      ∀ i,∃ E : CentripetalData (G := G) ((P i).fibre a),ApertureRestrictionData D E := by
  let f := T.focus.value a ha.1.1.1
  have hf := T.focus.family_graph_definable a ha.1.1.1
  let fA := rvFamilyMap (focusActive (A.fibre a) (T.active.fibre a)) f hf
  have hGraph := focusGraphParameterCode_at A T.active T.focus a ha.1.1.1
  have hAcode := (A.fibre_code a).symm
  have hTagged := (mem_taggedSourceParameterLocus_iff A.typedGraph a (A.fibre a) hAcode).mp ha.2.1.1.1
  have hIndependent := (mem_focusIndependentParameterLocus_map_iff
    (focusGraphParameterCode A T.active T.focus) a T.coordinate fA hGraph).mp ha.2.1.1.2
  have hLeading := (mem_focusLeadingTermParameterLocus_map_iff
    (focusGraphParameterCode A T.active T.focus) a T.coordinate fA hGraph).mp ha.2.1.2
  let F := fullFocusGraphOfContinuousFamily (A.fibre a) T.coordinate (T.active.fibre a) f hf
    (fun u => T.focus.value_continuous hv a ha.1.1.1 u) hA hAD hTagged hIndependent hLeading
  let c := vfScalarTemplateValue T.coefficient a ha.1.1.2
  let t := gammaTemplateRepresentative T.radius a ha.1.2
  have ht := gammaTemplateRepresentative_nonzero T.radius a ha.1.2
  have hGeo := focusMetadataParameterLocus_at T.coefficient T.radius (T.geometricLocus A P)
    a ha.1.1.2 ha.1.2 ha.2.2
  have hPos := (coefficientCodeCondition_at a c t).mp hGeo.1.1
  have hSource := (mem_focusSourceInvariantParameterLocus_map_iff A.typedGraph
    (focusGraphParameterCode A T.active T.focus) a c t ht T.coordinate fA hAcode hGraph).mp hGeo.1.2.1
  have hCov := (mem_focusErasedCovarianceParameterLocus_map_iff
    (focusGraphParameterCode A T.active T.focus) a c t ht T.coordinate fA hGraph).mp hGeo.1.2.2
  let W : PointwiseFocusCovariance F := {
    coefficient := c
    nonzero := hPos.1
    nonnegative := hPos.2
    coefficient_named := vfScalarTemplateValue_named T.coefficient a ha.1.1.2
    radius := GammaParameters.codeValue t.val
    radius_named := T.radius.value_named a ha.1.2
    source := hSource
    focus := hCov }
  let D := (W.fullData hcModel).component
  refine ⟨D,rfl,rfl,rfl,?_,?_⟩
  · intro q
    rw [D.extendedFocus_active q.property.1 q.property.2]
    exact F.focus_at q
  · intro i
    let fP := rvFamilyMap (focusActive ((P i).fibre a) (T.active.fibre a)) f hf
    have hPGraph := focusGraphParameterCode_at (P i) T.active T.focus a ha.1.1.1
    have hPMeta := (Set.mem_iInter.mp hGeo.2) i
    have hMove := (mem_focusSourceInvariantParameterLocus_map_iff (P i).typedGraph
      (focusGraphParameterCode (P i) T.active T.focus) a c t ht T.coordinate fP
        ((P i).fibre_code a).symm hPGraph).mp hPMeta
    exact ⟨((W.restrict (hPA i) (hP i) hMove).fullData hcModel).component,
      W.restrict_compatible hcModel (hPA i) (hP i) hMove⟩

end DiamondIntegral.Section6
