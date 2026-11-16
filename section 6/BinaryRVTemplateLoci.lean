import «section 6».ScalarRVTemplateLevels

/-! The parameter condition that a whole scalar RV-family graph takes
only the values zero and one is first-order over the original base.
All RV rows and every VF input are quantified in the same condition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p r n : ℕ}

def rvVFTemplateInputs (p r n : ℕ) : Set (Fin p ⊕ (Fin r ⊕ Fin n) → M) :=
  {z | z ∘ Sum.inr ∘ Sum.inl ∈ (rawRVSpace (M := M) r).domain ∧
    z ∘ Sum.inr ∘ Sum.inr ∈ (rawVFSpace (M := M) n).domain}

theorem rvVFTemplateInputs_definable : S.Definable LRV (rvVFTemplateInputs (M := M) p r n) :=
  (((rawRVSpace (M := M) r).definable_domain S).preimage_comp (Sum.inr ∘ Sum.inl)).inter
    (((rawVFSpace (M := M) n).definable_domain S).preimage_comp (Sum.inr ∘ Sum.inr))

def rvScalarBinaryParameterLocus (T : ContinuousRVGraphTemplate (M := M) S p r n 1) : Set (Fin p → M) :=
  forallRawParameterLocus ((rvVFTemplateInputs (M := M) p r n)ᶜ ∪
    (rvScalarTemplateLevel T iVFZero ∪ rvScalarTemplateLevel T iVFOne))

theorem rvScalarBinaryParameterLocus_definable
    (T : ContinuousRVGraphTemplate (M := M) S p r n 1) : S.Definable LRV (rvScalarBinaryParameterLocus T) :=
  forallRawParameterLocus_definable _
    (rvVFTemplateInputs_definable.compl.union
      ((rvScalarTemplateLevel_definable T iVFZero rawVFZero_constant_definable).union
        (rvScalarTemplateLevel_definable T iVFOne rawVFOne_constant_definable)))

theorem rvScalarBinaryParameterLocus_at
    (T : ContinuousRVGraphTemplate (M := M) S p r n 1) (a : Fin p → M) (ha : a ∈ T.good) :
    a ∈ rvScalarBinaryParameterLocus T ↔ ∀ u x,T.value a ha u x 0=0 ∨ T.value a ha u x 0=1 := by
  constructor
  · intro h u x
    have hRow := h (Sum.elim (rvValues u) (vfValues x))
    have hInput : Sum.elim a (Sum.elim (rvValues u) (vfValues x)) ∈ rvVFTemplateInputs (M := M) p r n :=
      ⟨⟨u,rfl⟩,⟨x,rfl⟩⟩
    rcases hRow with hBad | (hZero | hOne)
    · exact (hBad hInput).elim
    · exact Or.inl (Subtype.ext ((rvScalarTemplateLevel_at T a ha u x iVFZero).mp hZero))
    · exact Or.inr (Subtype.ext ((rvScalarTemplateLevel_at T a ha u x iVFOne).mp hOne))
  · intro h z
    by_cases hInput : Sum.elim a z ∈ rvVFTemplateInputs (M := M) p r n
    · right
      change z ∘ Sum.inl ∈ (rawRVSpace (M := M) r).domain ∧
        z ∘ Sum.inr ∈ (rawVFSpace (M := M) n).domain at hInput
      obtain ⟨u,hu⟩ := hInput.1
      obtain ⟨x,hx⟩ := hInput.2
      have he : Sum.elim (rvValues u) (vfValues x)=z := by
        funext i
        cases i with
        | inl i => exact congrFun hu i
        | inr i => exact congrFun hx i
      rw [← he]
      cases h u x with
      | inl hZero =>
        left
        exact (rvScalarTemplateLevel_at T a ha u x iVFZero).mpr (congrArg Subtype.val hZero)
      | inr hOne =>
        right
        exact (rvScalarTemplateLevel_at T a ha u x iVFOne).mpr (congrArg Subtype.val hOne)
    · exact Or.inl hInput

end DiamondIntegral.Section6
