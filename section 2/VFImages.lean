import «section 2».Atomic
import Section3.GammaProjection

/-! Logical image atomicity for an arbitrary finite VF source tuple.
This supplies the image-atomicity step separately from any geometric
classification of a definable image. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def vfFunctionGraph {n : ℕ} (A : Set (Fin n → M)) (f : (Fin n → M) → M) :
    Set (Fin (n + 1) → M) :=
  {z | Fin.init z ∈ A ∧ f (Fin.init z) = z (Fin.last n)}

/-- The scalar VF image is definable over exactly the graph's base. -/
theorem vf_function_image_definable (B : ParameterBase M) {n : ℕ}
    (A : Set (Fin n → M)) (f : (Fin n → M) → M)
    (hG : GammaParameters.DefinableOverBase B (fun _ : Fin (n + 1) => .vf)
      (vfFunctionGraph A f)) :
    GammaParameters.DefinableAtBase B .vf (f '' A) := by
  have hp := hG.image_real (fun _ : Fin 1 => Fin.last n)
  change GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .vf) {z | z 0 ∈ f '' A}
  convert hp using 1
  all_goals try rfl
  ext z
  constructor
  · rintro ⟨a, ha, hfa⟩
    let w : Fin (n + 1) → M := Fin.snoc a (f a)
    have hw : w ∈ vfFunctionGraph A f := by
      simpa only [vfFunctionGraph, w, Fin.init_snoc, Fin.snoc_last, Set.mem_ofPred_eq,
        and_true] using ha
    refine ⟨w, hw, ?_⟩
    funext j
    fin_cases j
    simpa [w, Function.comp_apply] using hfa
  · rintro ⟨w, ⟨hwa, hwf⟩, he⟩
    exact ⟨Fin.init w, hwa, hwf.trans (congrFun he 0)⟩

/-- Every definable scalar image of an atomic finite VF tuple set is atomic
at the original real/Gamma base. No geometric image conclusion is assumed. -/
theorem vf_function_image_atomic (B : ParameterBase M) {n : ℕ}
    (A : Set (Fin n → M)) (f : (Fin n → M) → M)
    (hA : IsAtomic B (fun _ => .vf) A)
    (hG : GammaParameters.DefinableOverBase B (fun _ : Fin (n + 1) => .vf)
      (vfFunctionGraph A f)) :
    IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ f '' A} := by
  have hI := vf_function_image_definable B A f hG
  refine ⟨hI, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hA.2.1
    exact ⟨fun _ => f a, ⟨a, ha, rfl⟩⟩
  · exact fun z hz j => GammaParameters.DefinableOverBase.proper hI z hz j
  · intro C hC
    have hcut := hG.inter
      (hC.preimage_real (fun _ : Fin (n + 1) => .vf) (fun _ : Fin 1 => Fin.last n))
    have hp := hcut.image_real Fin.castSucc
    let P : Set (Fin n → M) := {a | a ∈ A ∧ (fun _ : Fin 1 => f a) ∈ C}
    have hP : GammaParameters.DefinableOverBase B (fun _ => .vf) P := by
      convert hp using 1
      all_goals try rfl
      ext a
      constructor
      · rintro ⟨ha, hfa⟩
        let w : Fin (n + 1) → M := Fin.snoc a (f a)
        have hwG : w ∈ vfFunctionGraph A f := by
          simpa only [vfFunctionGraph, w, Fin.init_snoc, Fin.snoc_last, Set.mem_ofPred_eq,
            and_true] using ha
        have hwC : w ∘ (fun _ : Fin 1 => Fin.last n) ∈ C := by
          simpa only [w, Function.comp_def, Fin.snoc_last] using hfa
        refine ⟨w, ⟨hwG, hwC, hG.proper w hwG⟩, ?_⟩
        funext j
        simp only [w, Function.comp_apply, Fin.snoc_castSucc]
      · rintro ⟨w, ⟨⟨hwA, hwf⟩, hwC, _⟩, he⟩
        have hwa : Fin.init w = a := he
        change a ∈ A ∧ (fun _ : Fin 1 => f a) ∈ C
        refine ⟨hwa ▸ hwA, ?_⟩
        have heC : (fun _ : Fin 1 => f a) = w ∘ (fun _ : Fin 1 => Fin.last n) := by
          funext j
          exact (congrArg f hwa).symm.trans hwf
        rwa [heC]
    rcases hA.2.2.2 P hP with hsub | hdis
    · left
      intro z hz
      obtain ⟨a, ha, hfa⟩ := hz
      have hfaC : (fun _ : Fin 1 => f a) ∈ C := (hsub ha).2
      have he : (fun _ : Fin 1 => f a) = z := by
        funext j
        fin_cases j
        exact hfa
      rwa [he] at hfaC
    · right
      apply Set.disjoint_left.mpr
      intro z hz hzC
      obtain ⟨a, ha, hfa⟩ := hz
      have he : (fun _ : Fin 1 => f a) = z := by
        funext j
        fin_cases j
        exact hfa
      exact Set.disjoint_left.mp hdis ha ⟨ha, by rwa [he]⟩

end DiamondIntegral.Section2
