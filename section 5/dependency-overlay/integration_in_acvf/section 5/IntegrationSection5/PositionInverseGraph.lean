import IntegrationSection5.CellTranslationGeometry
import IntegrationSection5.CellGammaBridge

/-! The actual inverse positioning function and its complete original-base
graph, obtained by reversing the given bijection graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
open IntegrationInACVF.Section3ACVF
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}
variable {D E : Set (VF (M := M))} {f : VF (M := M) → VF (M := M)}

def positionInverse (h : Set.BijOn f D E) (b : VF (M := M)) : VF (M := M) :=
  if hb : b ∈ E then Classical.choose (h.surjOn hb) else 0

theorem positionInverse_mem (h : Set.BijOn f D E) (b : VF (M := M)) (hb : b ∈ E) :
    positionInverse h b ∈ D := by
  rw [positionInverse,dif_pos hb]
  exact (Classical.choose_spec (h.surjOn hb)).1

theorem positionInverse_right (h : Set.BijOn f D E) (b : VF (M := M)) (hb : b ∈ E) :
    f (positionInverse h b) = b := by
  rw [positionInverse,dif_pos hb]
  exact (Classical.choose_spec (h.surjOn hb)).2

theorem positionInverse_left (h : Set.BijOn f D E) (a : VF (M := M)) (ha : a ∈ D) :
    positionInverse h (f a) = a :=
  h.injOn (positionInverse_mem h (f a) (h.mapsTo ha)) ha (positionInverse_right h (f a) (h.mapsTo ha))

theorem positionInverse_gamma (h : Set.BijOn f D E)
    (hf : GammaParameters.DefinableOverBase G (fun _ : Fin 2 => .vf) (positionCodes D f)) :
    GammaParameters.DefinableOverBase G (fun _ : Fin 2 => .vf) (positionCodes E (positionInverse h)) := by
  let σ : Fin 2 → Fin 2 := ![1,0]
  have hRaw := FullBaseAtomicity.OverBase.preimage_comp (GammaBaseBridge.of_gamma G hf) σ
  have hEq : {z : Fin 2 → M | z ∘ σ ∈ positionCodes D f} = positionCodes E (positionInverse h) := by
    ext z
    constructor
    · rintro ⟨a,ha,he⟩
      refine ⟨f a,h.mapsTo ha,?_⟩
      funext j
      fin_cases j
      · exact congrFun he 1
      · rw [positionInverse_left h a ha]
        exact congrFun he 0
    · rintro ⟨b,hb,rfl⟩
      refine ⟨positionInverse h b,positionInverse_mem h b hb,?_⟩
      funext j
      fin_cases j
      · rfl
      · exact (congrArg Subtype.val (positionInverse_right h b hb)).symm
  apply GammaBaseDescent.to_gamma G (fun _ : Fin 2 => .vf) (positionCodes E (positionInverse h))
  · exact hEq ▸ hRaw
  · rintro z ⟨b,hb,rfl⟩ j
    fin_cases j
    · exact b.property
    · exact (positionInverse h b).property

end IntegrationInACVF.Section5
