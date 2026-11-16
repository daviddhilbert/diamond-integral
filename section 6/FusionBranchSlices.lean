import «section 6».FusionResidualContexts
import «section 6».ComplementaryBranchPreparation

/-! Full-set identities identify the core, release and residual
geometric constructions with the slices used in branch assembly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def PreparedSynchronizedFamily.transportSets
    {A C : DefSet (rawMixedSpace (M := M) n r) S}
    {P Q : I → DefSet (rawMixedSpace (M := M) n r) S}
    {hPA : ∀ i,(P i).carrier ⊆ A.carrier} {hQC : ∀ i,(Q i).carrier ⊆ C.carrier}
    (F : PreparedSynchronizedFamily (G := G) A P hPA) (hAC : A=C) (hPQ : ∀ i,P i=Q i) :
    PreparedSynchronizedFamily (G := G) C Q hQC := by
  cases hAC
  exact F.changePieces hPQ

variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
namespace CentripetalFusionRepair
variable (R : CentripetalFusionRepair (G := G) η T K A P C π σ)

def noncoreTags (_R : CentripetalFusionRepair (G := G) η T K A P C π σ) :=
  rvBooleanTagSet S (Fin.natAdd (n+1) (Fin.castAdd q (0 : Fin 1))) false

theorem stagePiece_subset (i : Fin k) : (R.stagePiece i).carrier ⊆ R.stageTarget.carrier := by
  rintro z ⟨p,hp⟩
  exact hp ▸ (R.stageMap.restrict (R.sourcePiece_subset i) p).property

theorem core_slice : R.component.coreRegularizedImage=focusActive R.stageTarget R.coreTags :=
  defSet_eq_of_carrier_eq rfl

theorem protected_core_slice (i : Fin k) :
    (R.protectedComponent i).coreRegularizedImage=focusActive (R.stagePiece i) R.coreTags := by
  rw [R.stagePiece_local_image]
  exact defSet_eq_of_carrier_eq rfl

theorem protected_release_slice
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) (i : Fin k) :
    (R.protectedComponent i).variableReleasedImage (R.releaseTags hCoeffMem)=
      focusActive (R.stagePiece i) (R.releaseTags hCoeffMem) := by
  rw [R.stagePiece_local_image]
  rfl

theorem stage_boolean_complement (h00 : M ⊨ Axioms.ACVF00) (z : Mixed M (n+1) ((n+1)+(1+q)))
    (hz : z ∈ R.stageTarget.carrier) : z.2 ∉ R.coreTags.carrier ↔ z.2 ∈ R.noncoreTags.carrier := by
  obtain ⟨p,hp⟩ := R.stage_preimage ⟨z,hz⟩
  change (R.stageMap p).val=z at hp
  rw [← hp]
  change ((regularize (R.component.point p.val)).2 ∉ (rvBooleanTagSet S _ true).carrier) ↔
    (regularize (R.component.point p.val)).2 ∈ (rvBooleanTagSet S _ false).carrier
  rw [regularized_boolean_tag_iff h00 R.component p.val true,
    regularized_boolean_tag_iff h00 R.component p.val false]
  exact Bool.eq_false_iff.symm

theorem noncore_complement_slice (h00 : M ⊨ Axioms.ACVF00)
    (Z : DefSet (rawMixedSpace (M := M) (n+1) ((n+1)+(1+q))) S) (hZ : Z.carrier ⊆ R.stageTarget.carrier) :
    focusActive Z (rvTagComplement R.coreTags)=focusActive Z R.noncoreTags := by
  apply defSet_eq_of_carrier_eq
  ext z
  change (z ∈ Z.carrier ∧ z.2 ∉ R.coreTags.carrier) ↔ (z ∈ Z.carrier ∧ z.2 ∈ R.noncoreTags.carrier)
  apply and_congr_right
  intro hz
  exact R.stage_boolean_complement h00 z (hZ hz)

theorem release_nested_slice
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (Z : DefSet (rawMixedSpace (M := M) (n+1) ((n+1)+(1+q))) S) :
    focusActive (focusActive Z R.noncoreTags) (R.releaseTags hCoeffMem)=focusActive Z (R.releaseTags hCoeffMem) := by
  apply defSet_eq_of_carrier_eq
  ext z
  change ((z ∈ Z.carrier ∧ z.2 ∈ R.noncoreTags.carrier) ∧ z.2 ∈ (R.releaseTags hCoeffMem).carrier) ↔
    (z ∈ Z.carrier ∧ z.2 ∈ (R.releaseTags hCoeffMem).carrier)
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.2⟩,h.2⟩⟩

theorem residual_nested_slice
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (Z : DefSet (rawMixedSpace (M := M) (n+1) ((n+1)+(1+q))) S) :
    focusActive (focusActive Z R.noncoreTags) (rvTagComplement (R.releaseTags hCoeffMem))=
      focusActive Z (R.residualTags hCoeffMem) := by
  apply defSet_eq_of_carrier_eq
  ext z
  change ((z ∈ Z.carrier ∧ z.2 ∈ R.noncoreTags.carrier) ∧ z.2 ∉ (R.releaseTags hCoeffMem).carrier) ↔
    (z ∈ Z.carrier ∧ z.2 ∈ R.noncoreTags.carrier ∧ z.2 ∉ (R.releaseTags hCoeffMem).carrier)
  exact and_assoc

end CentripetalFusionRepair
end DiamondIntegral.Section6
