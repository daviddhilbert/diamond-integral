import «section 6».SelectedJointDomains
import «section 6».ProgramPrimitiveImages

/-! A global regularization implements the local program's
regularization by selecting the new tail leading terms and retaining
the base labels. All actual protected images agree as full sets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q : ℕ}

def regularizedBaseLabels (π : Fin r → Fin q) : Fin r → Fin ((n+1)+q) := Fin.natAdd (n+1) ∘ π

def regularizedTailLabels (σ : Fin s → Fin q) : Fin (n+s) → Fin ((n+1)+q) :=
  Fin.addCases (fun i => Fin.castAdd q i.succ) (Fin.natAdd (n+1) ∘ σ)

theorem selectedUnaryBasePoint_regularize (π : Fin r → Fin q) (p : Mixed M (n+1) q) :
    selectedUnaryBasePoint (regularizedBaseLabels π) (regularize p)=selectedUnaryBasePoint π p := by
  apply Prod.ext
  · rfl
  · funext i
    simp only [selectedUnaryBasePoint,regularizedBaseLabels,Function.comp_apply,regularize,Fin.append_right]

theorem regularized_selected_tail (π : Fin r → Fin q) (σ : Fin s → Fin q) (p : Mixed M (n+1) q) :
    (Fin.tail (selectedJointPoint (regularizedBaseLabels π) (regularizedTailLabels σ) (regularize p)).1,
      (selectedJointPoint (regularizedBaseLabels π) (regularizedTailLabels σ) (regularize p)).2 ∘ Fin.natAdd r)=
        regularize (Fin.tail p.1,p.2 ∘ σ) := by
  apply Prod.ext
  · rfl
  · rw [selectedJointPoint_local]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Function.comp_apply,regularizedTailLabels,Fin.addCases_left,regularize,Fin.append_left]
      rfl
    · simp only [Function.comp_apply,regularizedTailLabels,Fin.addCases_right,regularize,Fin.append_right]

variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem selected_joint_regularization_mem_iff
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (A P : MixedSetParameterTemplate (M := M) S 1 n s)
    (hPA : ∀ b : B,(P.fibre (unaryFamilyParameter η b)).carrier ⊆
      (A.fibre (unaryFamilyParameter η b)).carrier)
    (π : Fin r → Fin q) (σ : Fin s → Fin q) (p : Mixed M (n+1) q)
    (b : B) (hb : selectedUnaryBasePoint π p=b.val) :
    selectedJointPoint (regularizedBaseLabels π) (regularizedTailLabels σ) (regularize p) ∈
      (unaryIndexedMixedFamily η ((CentripetalProgramTemplate.regularize s).pieceTarget A P)).carrier ↔
        selectedJointPoint π σ p ∈ (unaryIndexedMixedFamily η P).carrier := by
  have hbNew : unaryFamilyBasePoint
      (selectedJointPoint (regularizedBaseLabels π) (regularizedTailLabels σ) (regularize p))=b.val :=
    (selectedJointPoint_base _ _ _).trans ((selectedUnaryBasePoint_regularize π p).trans hb)
  rw [mem_unaryIndexedMixedFamily_at η _ _ b hbNew,
    mem_unaryIndexedMixedFamily_at η P _ b ((selectedJointPoint_base π σ p).trans hb),
    regularized_selected_tail,regularization_pieceTarget_mem_iff A P _ (hPA b)]
  rw [selectedJointPoint_local]
  rfl

theorem regularized_selected_family
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (A P : MixedSetParameterTemplate (M := M) S 1 n s)
    (hPA : ∀ b : B,(P.fibre (unaryFamilyParameter η b)).carrier ⊆
      (A.fibre (unaryFamilyParameter η b)).carrier)
    (C : DefSet (rawMixedSpace (M := M) (n+1) q) S) (π : Fin r → Fin q) (σ : Fin s → Fin q)
    (hBase : ∀ p ∈ C.carrier,selectedUnaryBasePoint π p ∈ B.carrier) :
    rvLabelPullback (regularizeMap C).image
      (Fin.addCases (regularizedBaseLabels π) (regularizedTailLabels σ))
      (unaryIndexedMixedFamily η ((CentripetalProgramTemplate.regularize s).pieceTarget A P))=
    ((regularization C).restrict
      (rvLabelPullback_subset C (Fin.addCases π σ) (unaryIndexedMixedFamily η P))).image := by
  apply defSet_eq_of_carrier_eq
  ext z
  constructor
  · intro hz
    obtain ⟨⟨p,hp⟩,hLocal⟩ := (mem_rvLabelPullback _ _ _ z).mp hz
    change regularize p.val=z at hp
    let b : B := ⟨selectedUnaryBasePoint π p.val,hBase p.val p.property⟩
    have hOld : selectedJointPoint π σ p.val ∈ (unaryIndexedMixedFamily η P).carrier := by
      apply (selected_joint_regularization_mem_iff η A P hPA π σ p.val b rfl).mp
      change selectedJointPoint (regularizedBaseLabels π) (regularizedTailLabels σ) z ∈ _ at hLocal
      exact hp.symm ▸ hLocal
    exact ⟨⟨p.val,(mem_rvLabelPullback C _ _ p.val).mpr ⟨p.property,hOld⟩⟩,hp⟩
  · rintro ⟨p,rfl⟩
    obtain ⟨hp,hOld⟩ := (mem_rvLabelPullback C _ _ p.val).mp p.property
    let b : B := ⟨selectedUnaryBasePoint π p.val,hBase p.val hp⟩
    apply (mem_rvLabelPullback _ _ _ _).mpr
    exact ⟨⟨⟨p.val,hp⟩,rfl⟩,
      (selected_joint_regularization_mem_iff η A P hPA π σ p.val b rfl).mpr hOld⟩

end DiamondIntegral.Section6
