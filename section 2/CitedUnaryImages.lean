import «section 2».PrimitiveDiscs
import «section 2».ScalarImages
import «section 2».AtomicBaseChange

/-! Lemmas 2.27–2.28 relative to the author's accepted inputs from [18].
Only the geometric conclusions are inputs. Ground-base atomicity of the
image is proved by the logical image theorem. The source's standing
nontrivial-value-group hypothesis and ACVF(0,0) remain explicit. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The geometric part of [18, Lemma 3.8], taken as an explicit input at
the author's instruction. This does not postulate image atomicity. -/
def PrimitiveImageInput (B : ParameterBase M) : Prop :=
  (M ⊨ Axioms.ACVF00) → NontrivialDefinableGamma B →
    ∀ (A : Set M) (f : M → M),
      IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ A} →
      IsPrimitiveDisc A →
      GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .vf) (scalarVFGraph A f) →
      IsPrimitiveDisc (f '' A)

/-- The nonconstant-image geometric part of [18, Lemma 3.13]. The original
base, characteristic and nontriviality hypotheses are retained. -/
def OpenDiscImageInput (B : ParameterBase M) : Prop :=
  (M ⊨ Axioms.ACVF00) → NontrivialDefinableGamma B →
    ∀ (A : Set M) (f : M → M),
      IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ A} →
      IsOpenDisc A →
      GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .vf) (scalarVFGraph A f) →
      (¬ ∃ c : M, ∀ x ∈ A, f x = c) → IsOpenDisc (f '' A)

/-- Lemma 2.27, relative only to the explicit cited geometric input.
The original-base atomicity of the image is proved independently here. -/
theorem lemma_2_27 (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M)
    (cited : PrimitiveImageInput B) (hΓ : NontrivialDefinableGamma B)
    (A : Set M) (f : M → M)
    (hA : IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ A})
    (hshape : IsPrimitiveDisc A)
    (hG : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .vf) (scalarVFGraph A f)) :
    IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ f '' A} ∧ IsPrimitiveDisc (f '' A) :=
  ⟨scalar_vf_image_atomic B A f hA hG, cited h00 hΓ A f hA hshape hG⟩

/-- Lemma 2.28, with an actual VF constant in the constant case. The image
atomicity in the other case is checked without a cited atomicity premise. -/
theorem lemma_2_28 (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M)
    (cited : OpenDiscImageInput B) (hΓ : NontrivialDefinableGamma B)
    (A : Set M) (f : M → M)
    (hA : IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ A})
    (hopen : IsOpenDisc A)
    (hG : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .vf) (scalarVFGraph A f)) :
    (∃ c : VF M, ∀ x ∈ A, f x = c.val) ∨
      (IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ f '' A} ∧ IsOpenDisc (f '' A)) := by
  have himage := scalar_vf_image_atomic B A f hA hG
  by_cases hc : ∃ c : M, ∀ x ∈ A, f x = c
  · obtain ⟨c, hc⟩ := hc
    obtain ⟨a, ha⟩ := hA.2.1
    have hcMem : c ∈ f '' A := ⟨a 0, ha, hc (a 0) ha⟩
    have hcSort := GammaParameters.DefinableAtBase.proper himage.1 c hcMem
    exact Or.inl ⟨⟨c, hcSort⟩, hc⟩
  · exact Or.inr ⟨himage, cited h00 hΓ A f hA hopen hG hc⟩

end DiamondIntegral.Section2
