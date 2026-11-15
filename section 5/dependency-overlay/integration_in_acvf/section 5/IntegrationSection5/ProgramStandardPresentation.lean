import IntegrationSection5.RVProjectionNormalization
import Section4.RVReindexing

/-! Source presentation identifications turn actual ordered programs into
standard contractions. The volume order is retained by an explicit RV iso. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}

def standardContractionOfProgram (A B : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n))
    (hB : B = vfPermutationImage A σ) {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S B U) : StandardContraction A σ := by
  cases hB
  exact ⟨l,U,T⟩

def standardProgramVolumeIso (A B : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n))
    (hB : B = vfPermutationImage A σ) {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S B U) :
    (standardContractionOfProgram A B σ hB T).contractionObject ≅
      @SpecialTransformations.Section4.RVObject.reindexVolume M
        (@CanonicalStructure.normalize M sM) S n n T.contractionObject σ.symm := by
  cases hB
  apply @SpecialTransformations.Section4.rvIsoOfVolumePreservingBijection M
    (@CanonicalStructure.normalize M sM) S n _ _ (Map.id _) Function.bijective_id
  intro a
  rfl

theorem vfPermutationImage_identity (A : DefSet (M := M) S n m) :
    vfPermutationImage A (Equiv.refl _) = A := by
  apply PresentedSet.eq_of_carrier_eq
  ext p
  constructor
  · rintro ⟨a,ha⟩
    change vfPermutation (Equiv.refl _) a.val = p at ha
    have h : vfPermutation (Equiv.refl (Fin n)) a.val = a.val := rfl
    rw [h] at ha
    exact ha ▸ a.property
  · intro hp
    exact ⟨⟨p,hp⟩,rfl⟩

end IntegrationInACVF.Section5
