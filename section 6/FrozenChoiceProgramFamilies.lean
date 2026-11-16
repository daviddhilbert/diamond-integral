import «section 6».UniformProgramFusion
import «section 6».FrozenInitialJointGeometry
import «section 6».TransportedProtectedFamilies

/-! Each actual prepared formula-choice base carries its prescribed
whole program, complete local geometry, all label-constant RV rows and
an original-base named uniform bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+1))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S}
namespace FrozenCoordinateProgramData

def choiceParameterMap (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) (i : Fin F.programs.count) :=
  (F.oldParameterMap h00).comp (Map.inclusion (F.choiceDomain_subset h00 i))

theorem exists_choice_uniform_program_family
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) (i : Fin F.programs.count) :
    Nonempty (UniformProgramFamily (F.choiceParameterMap h00 i) (F.programs.programs i).2
      (headFibreTemplate X.source) (fun j => headFibreTemplate (P j))) := by
  let incl := Map.inclusion (F.choiceDomain_subset h00 i)
  have hChoice (b : F.choiceDomain h00 i) :
      unaryFamilyParameter (F.oldParameterMap h00) (incl b) ∈ F.programs.choices i :=
    (F.mem_choiceDomain h00 i (incl b)).mp b.property
  obtain ⟨δ,hδ,hBound⟩ := F.uniform_named_target_data_bound h00 hc linear hκ hs hv hsmall hΓ
  refine ⟨{
    geometry := fun b => F.programs.geometry i _ (hChoice b)
    pullback := fun b => headFibreTemplate_rvPullback X.source X.pullback
      ((F.choiceParameterMap h00 i b).val 0)
    prepared := fun b => (F.programs.choices_subset i (hChoice b)).2
    rows := fun D hD b c hTags => F.selected_rows_on_target_labels h00 (incl b) (incl c) hTags i (hChoice b) D hD
    radius := δ
    named := hδ
    bound := fun D hD b => hBound (incl b) i (hChoice b) D hD }⟩

def initialProgramContext
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P) (hPX : ∀ i,(P i).carrier ⊆ X.source.carrier) :
    SelectedProgramContext (F.oldParameterMap h00) (headFibreTemplate X.source)
      (fun i => headFibreTemplate (P i)) U.target.source U.target.labels U.retainedLabels := by
  let Z := F.actualAmbientRefinement h00 U
  refine ⟨U.target.proper,U.target.doublyBounded,U.target.pullback,Z.source_subset,?_⟩
  intro i
  change ProperInvariant S (Z.selectedPiece
    (unaryIndexedMixedFamily (F.oldParameterMap h00) (headFibreTemplate (P i)))).carrier
  rw [F.actual_refinement_piece_eq h00 U hPX i]
  exact ((U.chain.atPiece i).literal_restriction h00 (hPX i)).target_properInvariant h00 hc hκ hs hv

end FrozenCoordinateProgramData
end DiamondIntegral.Section6
