import «section 6».MeasuredChoiceProgramRVData
import «section 6».MeasuredProgramChoicePartitions
import «section 6».FiniteHeadFormCompatiblePrograms

/-! Actual coordinate-fibre witnesses yield one finite original-base
program family, a disjoint formula-choice partition and complete
separately bounded RV-data rows. Only the lower-dimensional preparation
witnesses remain an induction premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure FiniteMeasuredCoordinateProgramData
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) where
  count : ℕ
  programs : Fin count → Σ s,CentripetalProgramTemplate (M := M) S 1 (n+1) r s
  choices : Fin count → Set (Fin 1 → M)
  choices_definable : ∀ i,S.Definable LRV (choices i)
  choices_subset : ∀ i,choices i ⊆ (rawVFSpace (M := M) 1).domain ∩
    (programs i).2.measuredFormGood (headFibreTemplate A) (fun j => headFibreTemplate (P j)) (headGammaFormTemplate ω)
  cover : ∀ a : VF M,∃ i,(fun _ : Fin 1 => a.val) ∈ choices i
  disjoint : ∀ i j a,a ∈ choices i → a ∈ choices j → i=j
  geometry : ∀ i,∀ a ∈ choices i,TemplateFibreGeometry (headFibreTemplate A) (fun j => headFibreTemplate (P j)) a

def FiniteMeasuredCoordinateProgramData.completeData
    {A : DefSet (rawMixedSpace (M := M) (n+2) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (F : FiniteMeasuredCoordinateProgramData A P ω) :=
  measuredChoiceProgramRVData F.programs (headFibreTemplate A) (fun i => headFibreTemplate (P i)) (headGammaFormTemplate ω) F.choices F.choices_definable

theorem FiniteMeasuredCoordinateProgramData.completeData_rows_bounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+2) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ A.carrier ∧ gammaFormExtension ω (x,u)=γ})
    (F : FiniteMeasuredCoordinateProgramData A P ω) (a : Fin 1 → M) :
    RVValueDoublyBounded (F.completeData.fibre a).carrier :=
by
  apply measuredChoiceProgramRVData_doublyBounded h00 hc hκ hs hv linear hsmall hΓ F.programs (headFibreTemplate A)
    (fun i => headFibreTemplate (P i)) (headGammaFormTemplate ω) F.choices F.choices_definable
      (fun i a ha => ⟨(F.choices_subset i ha).2.1.1.1,F.geometry i a ha⟩) _ a
  intro i z hz
  obtain ⟨b,rfl⟩ := (raw_unary_vf_parameter_iff z).mp (F.choices_subset i hz).1
  exact ⟨headGammaFormMap ω b,headGammaFormTemplate_section ω b,headGammaFormMap_levels_open ω b hLevels⟩

theorem exists_finite_measured_coordinate_program_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLocal : ∀ a : VF M,∃ F : MeasuredCoordinatePreparation (G := G)
      ((headFibreTemplate A).fibre (fun _ => a.val))
      (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val))
      (fun i => headFibreTemplate_subset (hPA i) a) (headGammaFormMap ω a),
        FormCompatibleSynchronizedChain (G := G) (Fin k)
          ((headFibreTemplate A).fibre (fun _ => a.val)) F.target F.map
          (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val)) (headGammaFormMap ω a)) :
    Nonempty (FiniteMeasuredCoordinateProgramData A P ω) := by
  obtain ⟨l,T,hCover⟩ := exists_finite_head_form_compatible_programs h00 hc linear hκ hs hv hsmall hΓ A hARV P hPA ω hLocal
  have hRawCover (a : Fin 1 → M) (ha : a ∈ (rawVFSpace (M := M) 1).domain) :
      ∃ i,a ∈ (T i).2.measuredFormGood (headFibreTemplate A) (fun j => headFibreTemplate (P j)) (headGammaFormTemplate ω) := by
    obtain ⟨b,rfl⟩ := (raw_unary_vf_parameter_iff a).mp ha
    exact hCover b
  obtain ⟨C,hC,hSub,hCCover,hDisj⟩ := exists_disjoint_measured_program_choice _
    ((rawVFSpace (M := M) 1).definable_domain S) (headFibreTemplate A) (fun j => headFibreTemplate (P j)) (headGammaFormTemplate ω) T hRawCover
  refine ⟨⟨l,T,C,hC,hSub,(fun a => hCCover _ ⟨(fun _ => a),rfl⟩),hDisj,?_⟩⟩
  intro i a ha
  obtain ⟨b,rfl⟩ := (raw_unary_vf_parameter_iff a).mp (hSub i ha).1
  exact coordinate_fibre_geometry A P hA hAD hPA hP b

end DiamondIntegral.Section6
