import «section 3».IntegrationMixedInverse
import IntegrationSection3ACVF.SeparationFunctions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A zero/nonzero output refinement removes the whole-VF alternative.
A zero image cannot be a paper-open ball, since those are infinite. -/
theorem integrationFibreConcentric_of_paper {r s : ℕ}
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    {A : Set (Section2.Mixed M 1 r)} {f : Section2.Mixed M 1 r → Section2.Mixed M 1 s}
    (h : IntegrationMixedPaperFibres A f)
    (hz : (∀ x ∈ A, (f x).1 0 = 0) ∨ (∀ x ∈ A, (f x).1 0 ≠ 0)) :
    Section2.FibreConcentric A f := by
  intro t u D hD hDA
  have hp : PaperBalls.IsOpenBall (Subtype.val '' ((fun x => (f ((fun _ => x),t)).1 0) '' D)) :=
    (h t u D hDA).mp ((integrationIsOpenBall_iff _).mpr (Or.inr hD))
  rcases hz with hz | hn
  · have hsub : Subtype.val '' ((fun x => (f ((fun _ => x),t)).1 0) '' D) ⊆ {(0 : Section2.VF M).val} := by
      rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact congrArg Subtype.val (hz _ (hDA x hx).1)
    exact ((SeparationFunctions.open_infinite h00 δ hδ hp).not_finite ((Set.finite_singleton _).subset hsub)).elim
  · rcases (integrationIsOpenBall_iff _).mp hp with he | hd
    · have hzero : (0 : Section2.VF M).val ∈ Subtype.val '' ((fun x => (f ((fun _ => x),t)).1 0) '' D) :=
        he.symm ▸ (0 : Section2.VF M).property
      obtain ⟨_,⟨x,hx,rfl⟩,heq⟩ := hzero
      exact (hn _ (hDA x hx).1 (Subtype.ext heq)).elim
    · exact hd

/-- Each Boolean source/target zero cell has the native finite-radius
disc-to-disc property in both directions. -/
theorem integrationHasDiscToDisc_of_paper {r s : ℕ}
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (A : Set (Section2.Mixed M 1 r)) (f : Section2.Mixed M 1 r → Section2.Mixed M 1 s)
    (hinj : Set.InjOn f A) (h : IntegrationMixedPaperFibres A f)
    (hsrc : (∀ x ∈ A, x.1 0 = 0) ∨ (∀ x ∈ A, x.1 0 ≠ 0))
    (htar : (∀ x ∈ A, (f x).1 0 = 0) ∨ (∀ x ∈ A, (f x).1 0 ≠ 0)) :
    Section2.HasDiscToDiscProperty A (f '' A) f := by
  letI : Nonempty (Section2.Mixed M 1 r) := ⟨((fun _ => 0),fun _ => Section2.rvZero M)⟩
  have hf : Set.BijOn f A (f '' A) := ⟨Set.mapsTo_image _ _,hinj,Set.surjOn_image f A⟩
  let g := Function.invFunOn f A
  have hi : Set.InvOn g f A (f '' A) := hf.invOn_invFunOn
  have hg : Set.BijOn g (f '' A) A := hf.symm hi.symm
  refine ⟨hf,integrationFibreConcentric_of_paper h00 δ hδ h htar,g,hg,hi,?_⟩
  apply integrationFibreConcentric_of_paper h00 δ hδ (h.inverse hg.mapsTo hi)
  rcases hsrc with hz | hn
  · exact Or.inl (fun y hy => hz _ (hg.mapsTo hy))
  · exact Or.inr (fun y hy => hn _ (hg.mapsTo hy))
end DiamondIntegral.Section3
