import «section 6».ChoiceProgramRVData
import «section 6».FiniteCoordinateFibrePrograms

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

theorem raw_unary_vf_parameter_iff (a : Fin 1 → M) :
    a ∈ (rawVFSpace (M := M) 1).domain ↔ ∃ b : VF M,a=(fun _ => b.val) := by
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v 0,?_⟩
    funext i
    fin_cases i
    exact (congrFun hv 0).symm
  · rintro ⟨b,rfl⟩
    exact ⟨(fun _ => b),rfl⟩

theorem coordinate_fibre_geometry
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier) (a : VF M) :
    TemplateFibreGeometry (headFibreTemplate A) (fun i => headFibreTemplate (P i)) (fun _ => a.val) :=
  ⟨headFibreTemplate_properInvariant A hA a,headFibreTemplate_doublyBounded A hAD a,
    (fun i => headFibreTemplate_subset (hPA i) a),(fun i => headFibreTemplate_properInvariant (P i) (hP i) a)⟩

structure FiniteCoordinateProgramData
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S) where
  count : ℕ
  programs : Fin count → Σ s,CentripetalProgramTemplate (M := M) S 1 n r s
  choices : Fin count → Set (Fin 1 → M)
  choices_definable : ∀ i,S.Definable LRV (choices i)
  choices_subset : ∀ i,choices i ⊆ (rawVFSpace (M := M) 1).domain ∩
    (programs i).2.preparedGood (headFibreTemplate A) (fun j => headFibreTemplate (P j))
  cover : ∀ a : VF M,∃ i,(fun _ : Fin 1 => a.val) ∈ choices i
  disjoint : ∀ i j a,a ∈ choices i → a ∈ choices j → i=j
  geometry : ∀ i,∀ a ∈ choices i,TemplateFibreGeometry (headFibreTemplate A) (fun j => headFibreTemplate (P j)) a

def FiniteCoordinateProgramData.completeData
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (F : FiniteCoordinateProgramData A P) :=
  choiceProgramRVData F.programs (headFibreTemplate A) (fun i => headFibreTemplate (P i)) F.choices F.choices_definable

theorem FiniteCoordinateProgramData.completeData_rows_bounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (F : FiniteCoordinateProgramData A P) (a : Fin 1 → M) :
    RVValueDoublyBounded (F.completeData.fibre a).carrier :=
  choiceProgramRVData_doublyBounded h00 hc hκ hs hv F.programs (headFibreTemplate A)
    (fun i => headFibreTemplate (P i)) F.choices F.choices_definable
      (fun i a ha => ⟨(F.choices_subset i ha).2.1,F.geometry i a ha⟩) a

theorem exists_finite_coordinate_program_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (hLocal : ∀ a : VF M,Nonempty (PreparedSynchronizedFamily (G := G)
      ((headFibreTemplate A).fibre (fun _ => a.val))
      (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val))
      (fun i => headFibreTemplate_subset (hPA i) a))) : Nonempty (FiniteCoordinateProgramData A P) := by
  obtain ⟨l,T,hCover⟩ := exists_finite_coordinate_fibre_programs h00 hc linear hκ hs hv hsmall hΓ A hARV P hPA hLocal
  have hRawCover (a : Fin 1 → M) (ha : a ∈ (rawVFSpace (M := M) 1).domain) :
      ∃ i,a ∈ (T i).2.preparedGood (headFibreTemplate A) (fun j => headFibreTemplate (P j)) := by
    obtain ⟨b,rfl⟩ := (raw_unary_vf_parameter_iff a).mp ha
    exact hCover b
  obtain ⟨C,hC,hSub,hCCover,hDisj⟩ := exists_disjoint_prepared_program_choice _
    ((rawVFSpace (M := M) 1).definable_domain S) (headFibreTemplate A) (fun j => headFibreTemplate (P j)) T hRawCover
  refine ⟨⟨l,T,C,hC,hSub,(fun a => hCCover _ ⟨(fun _ => a),rfl⟩),hDisj,?_⟩⟩
  intro i a ha
  obtain ⟨b,rfl⟩ := (raw_unary_vf_parameter_iff a).mp (hSub i ha).1
  exact coordinate_fibre_geometry A P hA hAD hPA hP b

end DiamondIntegral.Section6
