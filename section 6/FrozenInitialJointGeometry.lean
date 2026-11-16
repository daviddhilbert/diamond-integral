import «section 6».TransportedCoordinateFamilies
import «section 6».ProgramInitialDataEntries

/-! Discharge the joint initial-ambient geometry using the actual
prepared program data. No independent taggedness or uniform bound is
left as an input to the actual ambient refinement construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
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

def initialJointAmbient (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) :=
  unaryIndexedMixedFamily (F.oldParameterMap h00) (headFibreTemplate X.source)

theorem initial_rows_on_target_labels (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (b c : F.unary.target) (hTags : b.val.2=c.val.2) :
    ((leadingRVImageTemplate (headFibreTemplate X.source)).fibre
      (unaryFamilyParameter (F.oldParameterMap h00) b)).carrier=
      ((leadingRVImageTemplate (headFibreTemplate X.source)).fibre
        (unaryFamilyParameter (F.oldParameterMap h00) c)).carrier := by
  obtain ⟨i,hi⟩ := F.programs.cover ((F.oldParameterMap h00 b).val 0)
  exact F.selected_rows_on_target_labels h00 b c hTags i hi
    ⟨n+X.arity,leadingRVImageTemplate (headFibreTemplate X.source)⟩
    ((F.programs.programs i).2.initial_ambient_data_mem _ _)

theorem initialJointAmbient_rvPullback (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) :
    IsRVPullback (F.initialJointAmbient h00).carrier :=
  unaryIndexedMixedFamily_rvPullback F.unary.pullback (F.oldParameterMap h00) _
    (fun b => headFibreTemplate_rvPullback X.source X.pullback ((F.oldParameterMap h00 b).val 0))
    (F.initial_rows_on_target_labels h00)

theorem initialJointAmbient_tagged (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) :
    ∀ p ∈ (F.initialJointAmbient h00).carrier,∀ q ∈ (F.initialJointAmbient h00).carrier,
      p.2=q.2 → tupleRV M p.1=tupleRV M q.1 :=
  unaryIndexedMixedFamily_tagged F.unary.tagged (F.oldParameterMap h00) _
    (fun b => headFibreTemplate_rvPullback X.source X.pullback ((F.oldParameterMap h00 b).val 0))
    (F.initial_rows_on_target_labels h00)
    (fun b => headFibreTemplate_tagged X.source X.tagged ((F.oldParameterMap h00 b).val 0))

theorem initial_joint_named_row_bound
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) :
    ∃ δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      ∀ b : F.unary.target,∀ u ∈ ((leadingRVImageTemplate (headFibreTemplate X.source)).fibre
        (unaryFamilyParameter (F.oldParameterMap h00) b)).carrier,∀ j,
          (δ⁻¹).val ≤ Values.vrv (u j) ∧ Values.vrv (u j) ≤ δ.val := by
  obtain ⟨δ,hδ,hBound⟩ := F.uniform_named_target_data_bound h00 hc linear hκ hs hv hsmall hΓ
  refine ⟨δ,hδ,?_⟩
  intro b u hu j
  obtain ⟨i,hi⟩ := F.programs.cover ((F.oldParameterMap h00 b).val 0)
  exact hBound b i hi ⟨n+X.arity,leadingRVImageTemplate (headFibreTemplate X.source)⟩
    ((F.programs.programs i).2.initial_ambient_data_mem _ _) u hu j

theorem initialJointAmbient_geometry
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) :
    ProperInvariant S (F.initialJointAmbient h00).carrier ∧
      VFDoublyBounded (F.initialJointAmbient h00).carrier := by
  obtain ⟨δ,hδ,hRows⟩ := F.initial_joint_named_row_bound h00 hc linear hκ hs hv hsmall hΓ
  exact ⟨unaryIndexedMixedFamily_properInvariant h00 hc hκ hs hv F.unary.pullback
    F.unary.doublyBounded F.unary.proper.rvBounded (F.oldParameterMap h00) _
    (fun b => headFibreTemplate_rvPullback X.source X.pullback ((F.oldParameterMap h00 b).val 0))
    (F.initial_rows_on_target_labels h00) δ hRows,
    unaryIndexedMixedFamily_vfDoublyBounded F.unary.doublyBounded (F.oldParameterMap h00) _ δ hRows⟩

def actualAmbientRefinement (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P) : RVRefinementFrame (F.initialJointAmbient h00) :=
  F.ambientRefinementFrame h00 U (F.initialJointAmbient_tagged h00)

end FrozenCoordinateProgramData
end DiamondIntegral.Section6
