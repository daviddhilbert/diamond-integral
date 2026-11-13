import IntegrationSection3ACVF.OpenImages
import «section 3».IntegrationPrimitiveShapes
import «section 2».CitedUnaryImages
import Section3.GammaDefinableClosureField
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! The unary cited image interfaces are instantiated by checked [18]
proofs, using the exact original-base and point-set comparisons. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem integrationUnaryAtomic {B : GammaParameters.Base (M := M)} {A : Set M}
    (hA : Section2.IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ A}) :
    AdjoinBall.AtomicOver (integrationGammaBase B) A := by
  have ht := integrationGammaAtomic hA
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryParameters.unary_tuple_atomic_iff.mp ht

theorem integrationAtomic_neVF {B : GammaParameters.Base (M := M)} {A : Set M}
    (hA : Section2.IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ A}) :
    A ≠ {x | iVF x} := by
  intro he
  have hz : GammaParameters.DefinableAtBase B .vf {(0 : Section2.VF M).val} :=
    (GammaParameters.vfDefinableClosureFieldBase B).zero_mem
  rcases hA.2.2.2 {z | z 0 = (0 : Section2.VF M).val} hz with hs | hd
  · have hm : (fun _ : Fin 1 => (1 : Section2.VF M).val) ∈ {z | z 0 ∈ A} := by
      rw [he]
      exact (1 : Section2.VF M).property
    exact (one_ne_zero : (1 : Section2.VF M) ≠ 0) (Subtype.ext (hs hm))
  · have hm : (fun _ : Fin 1 => (0 : Section2.VF M).val) ∈ {z | z 0 ∈ A} := by
      rw [he]
      exact (0 : Section2.VF M).property
    exact Set.disjoint_left.mp hd hm rfl
/-- The geometric input [18, Lemma 3.8], supplied by its checked proof. -/
theorem integrationPrimitiveImageInput (B : GammaParameters.Base (M := M)) :
    Section2.PrimitiveImageInput B := by
  intro h00 hΓ A f hA hshape hG
  obtain ⟨δ,hd,hd1⟩ := integrationPositiveGamma_of_nontrivial B hΓ
  have hf : ∀ x ∈ A, iVF (f x) := by
    intro x hx
    exact hG.proper ![x,f x] ⟨hx,rfl⟩ 1
  have hi := PrimitiveImages.lemma_3_8 (integrationGammaBase B) h00 δ hd hd1
    (integrationUnaryAtomic hA) ((integrationPrimitive_iff A).mpr hshape)
    f (integrationGammaDefinable hG) hf
  exact (integrationPrimitive_iff (f '' A)).mp hi.2

/-- Diamond-integral Lemma 2.27 with the upstream geometric premise discharged. -/
theorem integration_lemma_2_27 (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B)
    (A : Set M) (f : M → M)
    (hA : Section2.IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ A})
    (hshape : Section2.IsPrimitiveDisc A)
    (hG : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .vf) (Section2.scalarVFGraph A f)) :
    Section2.IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ f '' A} ∧ Section2.IsPrimitiveDisc (f '' A) :=
  Section2.lemma_2_27 h00 B (integrationPrimitiveImageInput B) hΓ A f hA hshape hG

/-- The geometric input [18, Lemma 3.13], supplied by its checked proof. -/
theorem integrationOpenDiscImageInput (B : GammaParameters.Base (M := M)) :
    Section2.OpenDiscImageInput B := by
  intro h00 hΓ A f hA hopen hG hnonconstant
  obtain ⟨δ,hd,hd1⟩ := integrationPositiveGamma_of_nontrivial B hΓ
  have hOpen : PaperBalls.IsOpenBall A := (integrationIsOpenBall_iff A).mpr (Or.inr hopen)
  have hf : ∀ x ∈ A, iVF (f x) := by
    intro x hx
    exact hG.proper ![x,f x] ⟨hx,rfl⟩ 1
  rcases OpenImages.lemma_3_13 (integrationGammaBase B) h00 δ hd hd1 hOpen
      (integrationUnaryAtomic hA) f (integrationGammaDefinable hG) hf with hc | hi
  · exact (hnonconstant ⟨hc.choose.val,hc.choose_spec⟩).elim
  · have himage := Section2.scalar_vf_image_atomic B A f hA hG
    exact ((integrationIsOpenBall_iff (f '' A)).mp hi.2).resolve_left
      (integrationAtomic_neVF himage)

/-- Diamond-integral Lemma 2.28 with the upstream geometric premise discharged. -/
theorem integration_lemma_2_28 (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B)
    (A : Set M) (f : M → M)
    (hA : Section2.IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ A})
    (hopen : Section2.IsOpenDisc A)
    (hG : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .vf) (Section2.scalarVFGraph A f)) :
    (∃ c : Section2.VF M, ∀ x ∈ A, f x = c.val) ∨
      (Section2.IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ f '' A} ∧ Section2.IsOpenDisc (f '' A)) :=
  Section2.lemma_2_28 h00 B (integrationOpenDiscImageInput B) hΓ A f hA hopen hG
end DiamondIntegral.Section3
