import «section 6».PreparedUnaryRVMatching

/-! The actual Gamma quotient as a presentation in the original LRV
structure. Every nonzero RV representative is retained; no normalization
of the structure or representative choice changes the parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rawGammaPresentation : SpecialTransformations.DefinableGeometry.Space LRV M where
  Carrier := Gamma M
  Index := Fin 1
  finiteIndex := inferInstance
  domain := {z | GammaParameters.NonzeroRV (z 0)}
  domain_definable := GammaParameters.nonzero_rv_definable ∅
  decode z := GammaParameters.codeValue (z.val 0)
  onto := by
    intro γ
    obtain ⟨t,ht,hγ⟩ := GammaParameters.EndpointLogic.codeValue_surjective γ
    exact ⟨⟨fun _ => t,ht⟩,hγ⟩
  diagonal_definable := by
    have hLeft := (GammaParameters.nonzero_rv_definable (M := M) ∅).preimage_comp
      (Sum.inl : Fin 1 → Fin 1 ⊕ Fin 1)
    have hRight := (GammaParameters.nonzero_rv_definable (M := M) ∅).preimage_comp
      (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)
    have hLe := (GammaParameters.raw_le_definable (M := M) ∅).preimage_comp
      (![Sum.inl 0,Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)
    have hGe := (GammaParameters.raw_le_definable (M := M) ∅).preimage_comp
      (![Sum.inr 0,Sum.inl 0] : Fin 2 → Fin 1 ⊕ Fin 1)
    convert (hLeft.inter hRight).inter (hLe.inter hGe) using 1
    ext z
    constructor
    · rintro ⟨hx,hy,he⟩
      refine ⟨⟨hx,hy⟩,?_,?_⟩
      · exact (GammaParameters.original_le_codeValue_iff _ _ hx hy).mpr he.le
      · exact (GammaParameters.original_le_codeValue_iff _ _ hy hx).mpr he.ge
    · rintro ⟨⟨hx,hy⟩,hle,hge⟩
      exact ⟨hx,hy,le_antisymm
        ((GammaParameters.original_le_codeValue_iff _ _ hx hy).mp hle)
        ((GammaParameters.original_le_codeValue_iff _ _ hy hx).mp hge)⟩

end DiamondIntegral.Section6
