import «section 6».FrozenChoiceProgramFamilies
import «section 6».SelectedUnaryBaseRestrictions
import «section 6».FiniteTagPartitionPreparation

/-! Connect the actual frozen formula-choice family to finite
program fusion and assemble all choices, retaining the full unary lift
as a literal prefix on the original ambient and protected pieces. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
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

def choiceTags (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P) (i : Fin F.programs.count) :=
  selectedRVTagSet (pureRVTagDomain (F.choiceDomain h00 i)) U.target.labels

theorem choiceTags_cover (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P) (p : U.target.source) :
    ∃ i,p.val.2 ∈ (F.choiceTags h00 U i).carrier := by
  let b := U.target.projection p
  obtain ⟨i,hi⟩ := F.choiceDomain_cover h00 b
  refine ⟨i,⟨⟨b.val,hi⟩,?_⟩⟩
  exact congrArg Prod.snd (U.target.projection_value p)

theorem choiceTags_disjoint (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P)
    (i j : Fin F.programs.count) (u : Fin U.target.arity → RVInfinity M)
    (hi : u ∈ (F.choiceTags h00 U i).carrier) (hj : u ∈ (F.choiceTags h00 U j).carrier) : i=j := by
  obtain ⟨b,hb⟩ := hi
  obtain ⟨c,hc⟩ := hj
  let b' : F.unary.target := ⟨b.val,F.choiceDomain_subset h00 i b.property⟩
  let c' : F.unary.target := ⟨c.val,F.choiceDomain_subset h00 j c.property⟩
  have hTags : b.val.2=c.val.2 := hb.trans hc.symm
  have hcI : c.val ∈ (F.choiceDomain h00 i).carrier :=
    rvPullback_mem_of_sameRV (F.choiceDomain_rvPullback h00 i) b.property
      (F.unary.tagged b'.val b'.property c'.val c'.property hTags) hTags
  exact F.choiceDomain_disjoint h00 i j c' hcI c.property

def choiceProgramContext
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P) (hPX : ∀ j,(P j).carrier ⊆ X.source.carrier)
    (i : Fin F.programs.count) :
    SelectedProgramContext (F.choiceParameterMap h00 i) (headFibreTemplate X.source)
      (fun j => headFibreTemplate (P j)) (focusActive U.target.source (F.choiceTags h00 U i))
      U.target.labels U.retainedLabels :=
  (F.initialProgramContext h00 hc hκ hs hv U hPX).restrictUnaryBase
    (pureRVTagDomain (F.choiceDomain h00 i)) (F.choiceDomain_subset h00 i) (F.choiceDomain_eq_focusActive h00 i)

theorem choiceProgramContext_piece_eq
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P) (hPX : ∀ j,(P j).carrier ⊆ X.source.carrier)
    (i : Fin F.programs.count) (j : Fin l) :
    rvLabelPullback (focusActive U.target.source (F.choiceTags h00 U i))
      (Fin.addCases U.target.labels U.retainedLabels)
      (unaryIndexedMixedFamily (F.choiceParameterMap h00 i) (headFibreTemplate (P j)))=
    focusActive (U.map.restrict (hPX j)).image (F.choiceTags h00 U i) := by
  have hEq := (F.initialProgramContext h00 hc hκ hs hv U hPX).restricted_base_piece_eq
    (pureRVTagDomain (F.choiceDomain h00 i)) (F.choiceDomain_subset h00 i) (F.choiceDomain_eq_focusActive h00 i) j
  have hOld : rvLabelPullback U.target.source (Fin.addCases U.target.labels U.retainedLabels)
      (unaryIndexedMixedFamily (F.oldParameterMap h00) (headFibreTemplate (P j)))=
      (U.map.restrict (hPX j)).image := F.actual_refinement_piece_eq h00 U hPX j
  exact hEq.trans (congrArg (fun Q => focusActive Q (F.choiceTags h00 U i)) hOld)

theorem prepared_of_frozen_coordinate_program_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hIH : SynchronizedPreparationInDimension (G := G) S n l)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P) (hPX : ∀ j,(P j).carrier ⊆ X.source.carrier) :
    Nonempty (PreparedSynchronizedFamily (G := G) X.source P hPX) := by
  have hQProper (j) : ProperInvariant S (U.map.restrict (hPX j)).image.carrier :=
    ((U.chain.atPiece j).literal_restriction h00 (hPX j)).target_properInvariant h00 hc hκ hs hv
  have hChoicePrep (i : Fin F.programs.count) :
      Nonempty (PreparedSynchronizedFamily (G := G) (focusActive U.target.source (F.choiceTags h00 U i))
        (fun j => focusActive (U.map.restrict (hPX j)).image (F.choiceTags h00 U i))
        (fun j _ hp => ⟨U.image_subset hPX j hp.1,hp.2⟩)) := by
    obtain ⟨D⟩ := F.exists_choice_uniform_program_family h00 hc linear hκ hs hv hsmall hΓ i
    let Y := F.choiceProgramContext h00 hc hκ hs hv U hPX i
    obtain ⟨T'⟩ := synchronized_preparation_of_uniform_program h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt hIH
      (F.choiceDomain_properInvariant h00 i) (F.choiceDomain_rvPullback h00 i)
      (fun p hp z hz => F.unary.tagged p (F.choiceDomain_subset h00 i hp) z (F.choiceDomain_subset h00 i hz)) D Y
    exact ⟨T'.changePieces (fun j => F.choiceProgramContext_piece_eq h00 hc hκ hs hv U hPX i j)⟩
  obtain ⟨T'⟩ := synchronized_preparation_of_finite_tag_partition h00 hc hκ hs hv F.programs.count
    U.target.source U.target.proper U.target.doublyBounded U.target.pullback U.target.tagged
    (fun j => (U.map.restrict (hPX j)).image) (U.image_subset hPX) hQProper (F.choiceTags h00 U)
    (fun p hp => F.choiceTags_cover h00 U ⟨p,hp⟩) (F.choiceTags_disjoint h00 U) hChoicePrep
  exact ⟨T'.precompose hPX U.chain⟩

end FrozenCoordinateProgramData
end DiamondIntegral.Section6
