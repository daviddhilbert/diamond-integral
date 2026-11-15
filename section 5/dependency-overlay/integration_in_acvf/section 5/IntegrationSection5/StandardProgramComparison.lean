import IntegrationSection5.ProgramStandardPresentation
import IntegrationSection5.SurjectiveRVComparison

/-! Exact source, kernel and volume formulas for standard contractions
built from ordered programs, retaining the given VF-coordinate order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}

def standardProgramSourceMap (A B : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n))
    (hB : B = vfPermutationImage A σ) : Map A B :=
  Map.mk (fun a => ⟨vfPermutation σ a.val,by rw [hB]; exact (vfPermutationBijection A σ a).property⟩)
    (Map.graph_definable (vfPermutationBijection A σ))

theorem rawLabelMap_injective (U : DefSet (M := M) S 0 l) : Function.Injective (rawLabelMap U) := by
  intro a b h
  apply Subtype.ext
  refine Prod.ext (funext fun i => i.elim0) ?_
  exact congrArg Subtype.val h

theorem StandardContraction.toMap_surjective {A : DefSet (M := M) S n m} {σ : Equiv.Perm (Fin n)}
    (C : StandardContraction A σ) : Function.Surjective C.toMap :=
  C.program.surjective.comp (vfPermutationBijection_bijective A σ).2

theorem StandardContraction.rawContractionMap_surjective {A : DefSet (M := M) S n m}
    {σ : Equiv.Perm (Fin n)} (C : StandardContraction A σ) : Function.Surjective C.rawContractionMap := by
  rintro ⟨q,u,hu⟩
  obtain ⟨a,ha⟩ := C.toMap_surjective u
  refine ⟨a,Subtype.ext ?_⟩
  change (rawLabelMap C.target (C.toMap a)).val = q
  rw [ha]
  exact hu

theorem StandardContraction.raw_kernel {A : DefSet (M := M) S n m}
    {σ : Equiv.Perm (Fin n)} (C : StandardContraction A σ) (a b : A) :
    C.rawContractionMap a = C.rawContractionMap b ↔ C.toMap a = C.toMap b := by
  constructor
  · intro h
    apply rawLabelMap_injective C.target
    exact Subtype.ext (congrArg (fun u : rvObjectDomain C.contractionObject => u.val) h)
  · intro h
    exact congrArg (Map.toImage (rawLabelMap C.target)) h

theorem standardProgram_kernel (A B : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n))
    (hB : B = vfPermutationImage A σ) {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S B U) (a b : A) :
    (standardContractionOfProgram A B σ hB T).rawContractionMap a =
        (standardContractionOfProgram A B σ hB T).rawContractionMap b ↔
      T.toMap (standardProgramSourceMap A B σ hB a) = T.toMap (standardProgramSourceMap A B σ hB b) := by
  cases hB
  rw [StandardContraction.raw_kernel]
  rfl

theorem standardProgram_volume (A B : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n))
    (hB : B = vfPermutationImage A σ) {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S B U) (a : A) :
    (rvObjectVolume (standardContractionOfProgram A B σ hB T).contractionObject
      ((standardContractionOfProgram A B σ hB T).rawContractionMap a)).val =
        (rvObjectVolume T.contractionObject (T.rawContractionMap (standardProgramSourceMap A B σ hB a))).val ∘ σ.symm := by
  cases hB
  rfl

end IntegrationInACVF.Section5
