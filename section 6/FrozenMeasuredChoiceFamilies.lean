import «section 6».MeasuredUniformProgramFusion
import «section 6».FrozenChoiceFusion
import «section 6».FrozenMeasuredGeometricData
import «section 6».FrozenMeasuredProgramDataBounds

/-! Every actual frozen formula-choice domain has a uniform measured
family. Full local form graphs, all component guards and terminal Gamma
rows inherit one original-base named bound from the complete frozen data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.FrozenMeasuredCoordinateProgramData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+2))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+2) X.arity) S}
variable {ω : Map X.source (DefSet.univ (rawGammaPresentation (M := M)) S)}

theorem selected_measured_rows_on_target_labels (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω)
    (b c : F.unary.target) (hTags : b.val.2=c.val.2)
    (i : Fin F.programs.count) (hi : unaryFamilyParameter ((F.forget h00).oldParameterMap h00) b ∈ F.programs.choices i) :
    ∀ D ∈ (F.programs.programs i).2.measuredRVTrace (headFibreTemplate X.source)
        (fun j => headFibreTemplate (P j)) (headGammaFormTemplate ω),
      (D.2.fibre (unaryFamilyParameter ((F.forget h00).oldParameterMap h00) b)).carrier=
        (D.2.fibre (unaryFamilyParameter ((F.forget h00).oldParameterMap h00) c)).carrier := by
  let E := F.forget h00
  let p := F.unary.map.inverse (F.unary.chain.toChain.toSpecial.bijective h00) b
  let q := F.unary.map.inverse (F.unary.chain.toChain.toSpecial.bijective h00) c
  have hEq : (F.unary.map p).val.2=(F.unary.map q).val.2 := by
    simpa only [p,q,Map.apply_inverse] using hTags
  have hi' : F.substitution.value (fun _ => (p.val.1 0).val) ∈ F.programs.choices i := by
    rw [E.oldParameterMap_value h00] at hi
    exact hi
  intro D hD
  have h := F.selected_rows_constant h00 p q hEq i hi' D hD
  exact (congrArg (fun a => (D.2.fibre a).carrier) (E.oldParameterMap_value h00 b)).trans
    (h.trans (congrArg (fun a => (D.2.fibre a).carrier) (E.oldParameterMap_value h00 c)).symm)

theorem uniform_named_target_measured_bound
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ X.source.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    ∃ δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      ∀ b : F.unary.target,∀ i,unaryFamilyParameter ((F.forget h00).oldParameterMap h00) b ∈ F.programs.choices i →
        ∀ D ∈ (F.programs.programs i).2.measuredRVTrace (headFibreTemplate X.source)
          (fun j => headFibreTemplate (P j)) (headGammaFormTemplate ω),
        ∀ u ∈ (D.2.fibre (unaryFamilyParameter ((F.forget h00).oldParameterMap h00) b)).carrier,∀ j,
          (δ⁻¹).val ≤ Values.vrv (u j) ∧ Values.vrv (u j) ≤ δ.val := by
  obtain ⟨δ,hδ,hBound⟩ := F.uniform_named_bound h00 hc linear hκ hs hv hsmall hΓ hLevels
  refine ⟨δ,hδ,?_⟩
  intro b i hi D hD u hu j
  let E := F.forget h00
  let p := F.unary.map.inverse (F.unary.chain.toChain.toSpecial.bijective h00) b
  rw [E.oldParameterMap_value h00] at hi hu
  apply packedRVTrace_bound_on_entry h00
    (measuredChoiceProgramRVTrace F.programs.programs (headFibreTemplate X.source)
      (fun j => headFibreTemplate (P j)) (headGammaFormTemplate ω) F.programs.choices F.programs.choices_definable)
    (F.substitution.value (fun _ => (p.val.1 0).val)) δ (hBound p)
    ⟨D.1,D.2.restrictParameters (F.programs.choices i) (F.programs.choices_definable i)⟩
    (measuredChoiceProgramRVTrace_entry_mem F.programs.programs (headFibreTemplate X.source)
      (fun j => headFibreTemplate (P j)) (headGammaFormTemplate ω) F.programs.choices F.programs.choices_definable i D hD) u _ j
  exact ⟨hi,hu⟩

theorem exists_choice_uniform_measured_family
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ X.source.carrier ∧ gammaFormExtension ω (x,u)=γ})
    (i : Fin F.programs.count) :
    ∃ U : UniformMeasuredProgramFamily (G := G) ((F.forget h00).choiceParameterMap h00 i) (F.programs.programs i).2
      (headFibreTemplate X.source) (fun j => headFibreTemplate (P j)) (headGammaFormTemplate ω),
      ∀ b,U.forms b=headGammaFormMap ω ((((F.forget h00).choiceParameterMap h00 i) b).val 0) := by
  let E := F.forget h00
  let η := E.choiceParameterMap h00 i
  let incl := Map.inclusion (E.choiceDomain_subset h00 i)
  have hChoice (b : E.choiceDomain h00 i) : unaryFamilyParameter (E.oldParameterMap h00) (incl b) ∈ F.programs.choices i :=
    (E.mem_choiceDomain h00 i (incl b)).mp b.property
  obtain ⟨δ,hδ,hBound⟩ := F.uniform_named_target_measured_bound h00 hc linear hκ hs hv hsmall hΓ hLevels
  let U : UniformMeasuredProgramFamily (G := G) η (F.programs.programs i).2
      (headFibreTemplate X.source) (fun j => headFibreTemplate (P j)) (headGammaFormTemplate ω) := {
    geometry := fun b => F.programs.geometry i _ (hChoice b)
    pullback := fun b => headFibreTemplate_rvPullback X.source X.pullback ((η b).val 0)
    prepared := fun b => (F.programs.choices_subset i (hChoice b)).2.1.1
    rows := fun D hD b c hTags => F.selected_measured_rows_on_target_labels h00 (incl b) (incl c) hTags i (hChoice b)
      D (List.mem_append.mpr (Or.inl hD))
    radius := δ
    named := hδ
    bound := fun D hD b => hBound (incl b) i (hChoice b) D (List.mem_append.mpr (Or.inl hD))
    forms := fun b => headGammaFormMap ω ((η b).val 0)
    graphs := fun b => headGammaFormTemplate_section ω ((η b).val 0)
    levels := fun b => headGammaFormMap_levels_open ω ((η b).val 0) hLevels
    admissible := fun b => (F.programs.choices_subset i (hChoice b)).2
    measuredRows := fun D hD b c hTags => F.selected_measured_rows_on_target_labels h00 (incl b) (incl c) hTags i (hChoice b) D hD
    measuredBound := fun D hD b => hBound (incl b) i (hChoice b) D hD }
  exact ⟨U,fun _ => rfl⟩

end DiamondIntegral.Section6.FrozenMeasuredCoordinateProgramData
