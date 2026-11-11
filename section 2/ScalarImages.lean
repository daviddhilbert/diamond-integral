import «section 2».Atomic
import Section3.GammaProjection

/-! Original-base atomicity of definable scalar images. This logical part
of Lemmas 2.27–2.28 is proved here, separately from the cited geometry. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def scalarVFGraph (A : Set M) (f : M → M) : Set (Fin 2 → M) :=
  {z | z 0 ∈ A ∧ z 1 = f (z 0)}

private theorem scalar_image_definable (B : ParameterBase M) (A : Set M) (f : M → M)
    (hG : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .vf) (scalarVFGraph A f)) :
    GammaParameters.DefinableAtBase B .vf (f '' A) := by
  have hp := hG.image_real (fun _ : Fin 1 => (1 : Fin 2))
  change GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .vf) {z | z 0 ∈ f '' A}
  convert hp using 1
  all_goals try rfl
  ext z
  constructor
  · rintro ⟨x, hx, hfx⟩
    refine ⟨![x, f x], ⟨hx, rfl⟩, ?_⟩
    funext j
    fin_cases j
    exact hfx
  · rintro ⟨w, ⟨hwA, hwf⟩, he⟩
    have hwl : w 1 = z 0 := congrFun he 0
    exact ⟨w 0, hwA, hwf.symm.trans hwl⟩

/-- A ground-definable function sends an atomic unary set to an atomic
unary set over exactly the original real/Gamma base. -/
theorem scalar_vf_image_atomic (B : ParameterBase M) (A : Set M) (f : M → M)
    (hA : IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ A})
    (hG : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .vf) (scalarVFGraph A f)) :
    IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ f '' A} := by
  have hI := scalar_image_definable B A f hG
  refine ⟨hI, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hA.2.1
    exact ⟨fun _ => f (a 0), ⟨a 0, ha, rfl⟩⟩
  · exact fun z hz j => GammaParameters.DefinableOverBase.proper hI z hz j
  · intro C hC
    have hCut := hG.inter (hC.preimage_real (fun _ : Fin 2 => .vf) (fun _ : Fin 1 => (1 : Fin 2)))
    have hp := hCut.image_real (fun _ : Fin 1 => (0 : Fin 2))
    let P : Set (Fin 1 → M) := {z | z 0 ∈ A ∧ (fun _ : Fin 1 => f (z 0)) ∈ C}
    have hP : GammaParameters.DefinableOverBase B (fun _ => .vf) P := by
      convert hp using 1
      all_goals try rfl
      ext z
      constructor
      · rintro ⟨hzA, hzC⟩
        let w : Fin 2 → M := ![z 0, f (z 0)]
        have hwG : w ∈ scalarVFGraph A f := ⟨hzA, rfl⟩
        refine ⟨w, ⟨hwG, hzC, hG.proper w hwG⟩, ?_⟩
        funext j
        fin_cases j
        rfl
      · rintro ⟨w, ⟨⟨hwA, hwf⟩, hwC, _⟩, he⟩
        have hw0 : w 0 = z 0 := congrFun he 0
        have heC : (fun _ : Fin 1 => f (z 0)) = w ∘ (fun _ : Fin 1 => (1 : Fin 2)) := by
          funext j
          exact (hwf.trans (congrArg f hw0)).symm
        refine ⟨hw0 ▸ hwA, ?_⟩
        rw [heC]
        exact hwC
    rcases hA.2.2.2 P hP with hsub | hdis
    · left
      intro z hz
      obtain ⟨x, hx, hfx⟩ := hz
      have hxA : (fun _ : Fin 1 => x) ∈ {z | z 0 ∈ A} := hx
      have hfxC : (fun _ : Fin 1 => f x) ∈ C := (hsub hxA).2
      have he : (fun _ : Fin 1 => f x) = z := by
        funext j
        fin_cases j
        exact hfx
      rwa [he] at hfxC
    · right
      apply Set.disjoint_left.mpr
      intro z hz hzC
      obtain ⟨x, hx, hfx⟩ := hz
      have hxA : (fun _ : Fin 1 => x) ∈ {z | z 0 ∈ A} := hx
      have he : (fun _ : Fin 1 => f x) = z := by
        funext j
        fin_cases j
        exact hfx
      have hxP : (fun _ : Fin 1 => x) ∈ P := ⟨hx, by rwa [he]⟩
      exact Set.disjoint_left.mp hdis hxA hxP

end DiamondIntegral.Section2
