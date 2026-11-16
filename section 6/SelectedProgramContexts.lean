import «section 6».SelectedRegularizationStages
import «section 6».UniformProgramFamilies
import «section 6».ProgramInitialDataEntries
import «section 6».PreparedSynchronizedFamilies

/-! The actual source invariant for finite fusion, with arbitrary
retained labels. The terminal case and the regularization step construct
literal synchronized chains and exact protected images. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def PreparedSynchronizedFamily.identity
    {C : DefSet (rawMixedSpace (M := M) n q) S}
    (hC : ProperInvariant S C.carrier) (hD : VFDoublyBounded C.carrier) (hRP : IsRVPullback C.carrier)
    (P : I → DefSet (rawMixedSpace (M := M) n q) S)
    (hPC : ∀ i,(P i).carrier ⊆ C.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (hPRP : ∀ i,IsRVPullback (P i).carrier) : PreparedSynchronizedFamily (G := G) C P hPC where
  arity := q
  target := C
  map := Map.id C
  chain := .identity C hC P hPC hP
  proper := hC
  doublyBounded := hD
  pullback := hRP
  prepared i := by
    have he : ((Map.id C).restrict (hPC i)).image=P i := by
      apply defSet_eq_of_carrier_eq
      ext p
      exact ⟨fun ⟨a,ha⟩ => ha ▸ a.property,fun hp => ⟨⟨p,hp⟩,rfl⟩⟩
    rw [he]
    exact hPRP i

variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

structure SelectedProgramContext
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (A : MixedSetParameterTemplate (M := M) S 1 n s)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s)
    (C : DefSet (rawMixedSpace (M := M) (n+1) q) S) (π : Fin r → Fin q) (σ : Fin s → Fin q) : Prop where
  proper : ProperInvariant S C.carrier
  doublyBounded : VFDoublyBounded C.carrier
  pullback : IsRVPullback C.carrier
  source : ∀ p ∈ C.carrier,selectedJointPoint π σ p ∈ (unaryIndexedMixedFamily η A).carrier
  piecesProper : ∀ i,ProperInvariant S
    (rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))).carrier

namespace SelectedProgramContext
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}

theorem base (X : SelectedProgramContext η A P C π σ) :
    ∀ p ∈ C.carrier,selectedUnaryBasePoint π p ∈ B.carrier := by
  intro p hp
  obtain ⟨b,hb,hA⟩ := (mem_unaryIndexedMixedFamily η A _).mp (X.source p hp)
  rw [selectedJointPoint_base] at hb
  exact hb.symm ▸ b.property

def terminal (hB : IsRVPullback B.carrier) (X : SelectedProgramContext η A P C π σ)
    (U : UniformProgramFamily η (.identity s) A P) :
    PreparedSynchronizedFamily (G := G) C
      (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
      (fun i => rvLabelPullback_subset C _ _) :=
  PreparedSynchronizedFamily.identity X.proper X.doublyBounded X.pullback _ _ X.piecesProper
    (fun i => selected_joint_family_rvPullback hB η (P i) C X.pullback π σ
      (fun b => U.identity_prepared b i)
      (U.rows _ ((CentripetalProgramTemplate.identity s).initial_piece_data_mem A P i)))

def afterRegularization
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : SelectedProgramContext η A P C π σ)
    (hPA : ∀ b : B,∀ i,((P i).fibre (unaryFamilyParameter η b)).carrier ⊆
      (A.fibre (unaryFamilyParameter η b)).carrier) :
    SelectedProgramContext η ((CentripetalProgramTemplate.regularize s).target A)
      (fun i => (CentripetalProgramTemplate.regularize s).pieceTarget A (P i)) (regularizeMap C).image
      (regularizedBaseLabels π) (regularizedTailLabels σ) := by
  have hChain : SynchronizedCentripetalChain (G := G) (Fin k) C (regularizeMap C).image (regularization C)
      (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))) :=
    .regularize C X.proper X.doublyBounded _ (fun i => rvLabelPullback_subset C _ _) X.piecesProper
      (fun i => X.doublyBounded.mono (rvLabelPullback_subset C _ _))
  refine ⟨regularization_properInvariant h00 hc hκ hs hv C X.proper X.doublyBounded,
    regularized_vfDoublyBounded X.doublyBounded,regularization_rvPullback C X.pullback,?_,?_⟩
  · rintro z ⟨p,rfl⟩
    let b : B := ⟨selectedUnaryBasePoint π p.val,X.base p.val p.property⟩
    exact (selected_joint_regularization_mem_iff η A A (fun _ => Set.Subset.refl _) π σ p.val b rfl).mpr
      (X.source p.val p.property)
  · intro i
    rw [regularized_selected_family η A (P i) (fun b => hPA b i) C π σ X.base]
    exact ((hChain.atPiece i).literal_restriction h00 (rvLabelPullback_subset C _ _)).target_properInvariant
      h00 hc hκ hs hv

end SelectedProgramContext
end DiamondIntegral.Section6
