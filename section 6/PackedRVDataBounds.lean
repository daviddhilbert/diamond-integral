import «section 6».PackedRVDataTraces
import «section 6».FrozenProgramDataUniformBounds

/-! The uniform bound for a complete packed row bounds each actual
constituent with the same radius. In particular every selected program
locus, intermediate image, coefficient and Gamma name inherits it. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p r n k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem packedRVTrace_bound_on_entry (h00 : M ⊨ Axioms.ACVF00)
    (D : List (RVDataTemplate (M := M) S p)) (a : Fin p → M) (δ : Gamma M)
    (hBound : ∀ u ∈ ((packedRVTrace D).fibre a).carrier,∀ j,
      (δ⁻¹).val ≤ Values.vrv (u j) ∧ Values.vrv (u j) ≤ δ.val)
    (T : RVDataTemplate (M := M) S p) (hT : T ∈ D) :
    ∀ u ∈ (T.2.fibre a).carrier,∀ j,(δ⁻¹).val ≤ Values.vrv (u j) ∧ Values.vrv (u j) ≤ δ.val := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hT
  cases hi
  intro u hu j
  have hPacked : rvDataPack (L := rvTraceMaxArity D) i u ∈ ((packedRVTrace D).fibre a).carrier :=
    (mem_packedRVDataFamily_iff h00 (fun i : Fin D.length => (D.get i).2) (rvTraceArity_le D) a i u).mpr hu
  have h := hBound _ hPacked (Fin.castAdd D.length (Fin.castLE (rvTraceArity_le D i) j))
  rwa [rvDataPack_input (rvTraceArity_le D i)] at h

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+1))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S}

theorem FrozenCoordinateProgramData.uniform_named_selected_data_bound
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) :
    ∃ δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      ∀ p : A,∀ i,F.substitution.value (fun _ => (p.val.1 0).val) ∈ F.programs.choices i →
        ∀ D ∈ (F.programs.programs i).2.rvTrace (headFibreTemplate X.source) (fun j => headFibreTemplate (P j)),
        ∀ u ∈ (D.2.fibre (F.substitution.value (fun _ => (p.val.1 0).val))).carrier,∀ j,
          (δ⁻¹).val ≤ Values.vrv (u j) ∧ Values.vrv (u j) ≤ δ.val := by
  obtain ⟨δ,hδ,hBound⟩ := F.uniform_named_bound h00 hc linear hκ hs hv hsmall hΓ
  refine ⟨δ,hδ,?_⟩
  intro p i hi D hD u hu j
  apply packedRVTrace_bound_on_entry h00
    (choiceProgramRVTrace F.programs.programs (headFibreTemplate X.source)
      (fun j => headFibreTemplate (P j)) F.programs.choices F.programs.choices_definable)
    (F.substitution.value (fun _ => (p.val.1 0).val)) δ (hBound p)
    ⟨D.1,D.2.restrictParameters (F.programs.choices i) (F.programs.choices_definable i)⟩
    (choiceProgramRVTrace_entry_mem F.programs.programs (headFibreTemplate X.source)
      (fun j => headFibreTemplate (P j)) F.programs.choices F.programs.choices_definable i D hD) u _ j
  exact ⟨hi,hu⟩

end DiamondIntegral.Section6
