import «section 6».UnaryFirstZeroEndpoints

/-! The actual variable cutoff is exactly a prescribed original core.
Consequently it cannot capture part of a different separated core, and
the branch is constant on every entire prescribed original core. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFirstZeroState
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r₀ r s : ℕ}
variable {A₀ : DefSet (rawMixedSpace (M := M) 1 r₀) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {K : UnaryCorePlan A₀}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s} {j : Fin r}
variable (D : SpecialTransformations.Section5.Focus A 0 j)
variable (tail : SpecialTransformations.Section5.Chain R 1 D.etaImage B)
variable (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S)
  (.cons (.centripetal D) tail))
variable (Z : UnaryFirstZeroState (G := G) hc K (.cons (.centripetal D) tail) hT)
variable (h00 : M ⊨ Axioms.ACVF00)

theorem firstZeroAperture_endpoint_at
    (p : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) :
    (Z.firstZeroAperture D tail hT h00).endpoint p.val.2=
      (K.offset (Z.firstZeroCentreMap D tail hT h00 p)).val 0 :=
  scalarRVValue_at _ (Z.firstZeroEndpointMap_same_labels D tail hT h00) p

theorem firstZeroCentreMap_tags
    (p : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) :
    (Z.map (K.centre (Z.firstZeroCentreMap D tail hT h00 p))).val.2=p.val.2 := by
  have h := congrArg (fun a : Z.frame.current => a.val.2) (Z.firstZeroCentreMap_point D tail hT h00 p)
  have hTags := congrArg (fun a : Mixed M 1 Z.arity => a.2)
    ((Z.frame.wholeFocusData D hT.1.2).focusPointMap_value Z.pullback p)
  exact h.trans hTags

theorem firstZeroCentreMap_field
    (p : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) :
    (Z.map (K.centre (Z.firstZeroCentreMap D tail hT h00 p))).val.1 0=
      (Z.frame.wholeFocusData D hT.1.2).focus p.val.2 := by
  have h := congrArg (fun a : Z.frame.current => a.val.1 0) (Z.firstZeroCentreMap_point D tail hT h00 p)
  have hField := congrArg (fun a : Mixed M 1 Z.arity => a.1 0)
    ((Z.frame.wholeFocusData D hT.1.2).focusPointMap_value Z.pullback p)
  exact h.trans hField

theorem firstZero_capture_exact
    (p : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) (a : A₀) :
    ((Z.map a).val.2=p.val.2 ∧ (Z.firstZeroAperture D tail hT h00).core (Z.map a).val=true) ↔
      a.val ∈ K.disc (Z.firstZeroCentreMap D tail hT h00 p) := by
  let c := Z.firstZeroCentreMap D tail hT h00 p
  have hTags : (Z.map (K.centre c)).val.2=p.val.2 := Z.firstZeroCentreMap_tags D tail hT h00 p
  have hActive : (Z.map (K.centre c)).val.2 ∈ (Z.firstZeroAperture D tail hT h00).focusData.activeTags.carrier := by
    rw [hTags]
    exact p.property.2
  have hFocus : (Z.firstZeroAperture D tail hT h00).focusData.focus (Z.map (K.centre c)).val.2=
      (Z.map (K.centre c)).val.1 0 := by
    rw [hTags]
    exact (Z.firstZeroCentreMap_field D tail hT h00 p).symm
  have hEndpoint : vfValue ((Z.firstZeroAperture D tail hT h00).endpoint (Z.map (K.centre c)).val.2)=
      (K.radius c).val := by
    rw [hTags,Z.firstZeroAperture_endpoint_at D tail hT h00 p]
    rfl
  have h := (Z.core_chart c).capture_exact Z.source_pullback (K.centre_nonzero c)
    (K.source_bound c).le (Z.chain.bijective h00).injective
    (Z.firstZeroAperture D tail hT h00) hActive hFocus hEndpoint a
  rw [hTags] at h
  exact h

theorem firstZero_core_false_of_inactive (a : A₀)
    (hInactive : (Z.map a).val.2 ∉ (Z.frame.wholeFocusData D hT.1.2).activeTags.carrier) :
    (Z.firstZeroAperture D tail hT h00).core (Z.map a).val=false := by
  let E := Z.firstZeroAperture D tail hT h00
  have hF : E.extendedFocus (Z.map a).val=(0 : VF M) :=
    Subtype.ext (UnaryRelativeApertureData.scalarExtension_inactive E.focusMap hInactive)
  have hE : E.extendedEndpoint (Z.map a).val=(0 : VF M) :=
    Subtype.ext (UnaryRelativeApertureData.scalarExtension_inactive E.endpointMap hInactive)
  change decide (vfValue (E.extendedEndpoint (Z.map a).val)<
    vfValue ((Z.map a).val.1 E.coordinate-E.extendedFocus (Z.map a).val))=false
  rw [hF,hE,value_zero]
  exact decide_eq_false (not_lt_of_ge (Values.le_infinity _))

theorem firstZero_core_implies_disc (a : A₀)
    (hCore : (Z.firstZeroAperture D tail hT h00).core (Z.map a).val=true) :
    ∃ c : K.centres,(Z.map (K.centre c)).val.2 ∈ Z.frame.liveLabels.carrier ∧ a.val ∈ K.disc c := by
  have hActive : (Z.map a).val.2 ∈ (Z.frame.wholeFocusData D hT.1.2).activeTags.carrier := by
    by_contra hn
    have hf := Z.firstZero_core_false_of_inactive D tail hT h00 a hn
    rw [hf] at hCore
    contradiction
  let p : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags :=
    ⟨(Z.map a).val,(Z.map a).property,hActive⟩
  refine ⟨Z.firstZeroCentreMap D tail hT h00 p,?_,?_⟩
  · rw [Z.firstZeroCentreMap_tags D tail hT h00 p]
    exact Z.frame.activeTags_live D hT.1.2 hActive
  · exact (Z.firstZero_capture_exact D tail hT h00 p a).mp ⟨rfl,hCore⟩

theorem firstZero_core_constant (p : K.centres) (a : A₀) (ha : a.val ∈ K.disc p) :
    (Z.firstZeroAperture D tail hT h00).core (Z.map a).val=
      (Z.firstZeroAperture D tail hT h00).core (Z.map (K.centre p)).val := by
  have hTags := (Z.core_chart p).tags a ha.1 ha.2
  have hIff : (Z.firstZeroAperture D tail hT h00).core (Z.map a).val=true ↔
      (Z.firstZeroAperture D tail hT h00).core (Z.map (K.centre p)).val=true := by
    constructor
    · intro hCore
      obtain ⟨c,hLive,hDisc⟩ := Z.firstZero_core_implies_disc D tail hT h00 a hCore
      have he : c=p := by
        by_contra hn
        exact Set.disjoint_left.mp (K.separated c p hn) hDisc ha
      subst c
      have hActive : (Z.map a).val.2 ∈ (Z.frame.wholeFocusData D hT.1.2).activeTags.carrier := by
        by_contra hn
        rw [Z.firstZero_core_false_of_inactive D tail hT h00 a hn] at hCore
        contradiction
      let z : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags :=
        ⟨(Z.map a).val,(Z.map a).property,hActive⟩
      have hDisc' := (Z.firstZero_capture_exact D tail hT h00 z a).mp ⟨rfl,hCore⟩
      have he' : Z.firstZeroCentreMap D tail hT h00 z=p := by
        by_contra hn
        exact Set.disjoint_left.mp (K.separated _ _ hn) hDisc' ha
      have hpDisc : (K.centre p).val ∈ K.disc (Z.firstZeroCentreMap D tail hT h00 z) := by
        rw [he']
        exact K.centre_mem_disc p
      exact ((Z.firstZero_capture_exact D tail hT h00 z (K.centre p)).mpr hpDisc).2
    · intro hCore
      have hActive : (Z.map (K.centre p)).val.2 ∈ (Z.frame.wholeFocusData D hT.1.2).activeTags.carrier := by
        by_contra hn
        rw [Z.firstZero_core_false_of_inactive D tail hT h00 (K.centre p) hn] at hCore
        contradiction
      let z : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags :=
        ⟨(Z.map (K.centre p)).val,(Z.map (K.centre p)).property,hActive⟩
      have hpDisc := (Z.firstZero_capture_exact D tail hT h00 z (K.centre p)).mp ⟨rfl,hCore⟩
      have he : Z.firstZeroCentreMap D tail hT h00 z=p :=
        (K.centre_unique_in_disc p _ hpDisc).symm
      have haDisc : a.val ∈ K.disc (Z.firstZeroCentreMap D tail hT h00 z) := by
        rw [he]
        exact ha
      exact ((Z.firstZero_capture_exact D tail hT h00 z a).mpr haDisc).2
  cases h₁ : (Z.firstZeroAperture D tail hT h00).core (Z.map a).val <;>
    cases h₂ : (Z.firstZeroAperture D tail hT h00).core (Z.map (K.centre p)).val <;> simp_all

end DiamondIntegral.Section6.UnaryFirstZeroState
