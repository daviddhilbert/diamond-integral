import «section 3».FullRawLogic
import IntegrationSection3ACVF.FullGammaSyntax
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : FullBaseAtomicity.Base (M := M)} {α β ι : Type} [Finite α] [Finite β] [Finite ι]

/-- A function on actual Gamma tuples with its entire code graph definable. -/
def FullGammaFunction (B : FullBaseAtomicity.Base (M := M))
    {α : Type} [Finite α] (f : (α → Values.Gamma (M := M)) → Values.Gamma (M := M)) : Prop :=
  FullGammaSyntax.Definable B (fun z : α ⊕ Fin 1 → Values.Gamma (M := M) => f (z ∘ Sum.inl) = z (.inr 0))

namespace FullGammaFunction

theorem proj (B : FullBaseAtomicity.Base (M := M)) (i : α) :
    FullGammaFunction B (fun z : α → Values.Gamma (M := M) => z i) :=
  FullGammaSyntax.eq_definable B (Sum.inl i : α ⊕ Fin 1) (Sum.inr 0)

theorem constant (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) :
    FullGammaFunction B (fun _ : α → Values.Gamma (M := M) => δ) := by
  apply (FullGammaSyntax.unary_at hδ (Sum.inr (0 : Fin 1) : α ⊕ Fin 1)).congr
  intro z
  exact Set.mem_singleton_iff.trans eq_comm

theorem one (B : FullBaseAtomicity.Base (M := M)) :
    FullGammaFunction B (fun _ : α → Values.Gamma (M := M) => 1) :=
  constant 1 (FullGammaSyntax.one_definable B)

theorem reindex {f : (α → Values.Gamma (M := M)) → Values.Gamma (M := M)}
    (hf : FullGammaFunction B f) (e : α → β) :
    FullGammaFunction B (fun z => f (z ∘ e)) := by
  have hh := FullGammaSyntax.Definable.reindex hf (Sum.map e (id : Fin 1 → Fin 1))
  exact hh

/-- Substitution uses existential full-code graphs, so no Gamma section
or extra real parameter enters the base. -/
theorem substitute {P : (ι → Values.Gamma (M := M)) → Prop}
    (hP : FullGammaSyntax.Definable B P)
    (f : ι → (α → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : ∀ i, FullGammaFunction B (f i)) :
    FullGammaSyntax.Definable B (fun z => P (fun i => f i z)) := by
  have hgraphs := FullGammaSyntax.Definable.forall_finite (fun i =>
    FullGammaSyntax.Definable.reindex (hf i) (Sum.elim (Sum.inl : α → α ⊕ ι) (fun _ : Fin 1 => Sum.inr i)))
  have hh := (hgraphs.and (hP.reindex (Sum.inr : ι → α ⊕ ι))).exists_block
  apply hh.congr
  intro z
  change (∃ u : ι → Values.Gamma (M := M), (∀ i, f i z = u i) ∧ P u) ↔ P (fun i => f i z)
  exact ⟨fun ⟨u,hu,hp⟩ => (funext hu).symm ▸ hp,fun hp => ⟨fun i => f i z,fun _ => rfl,hp⟩⟩

theorem mul {f g : (α → Values.Gamma (M := M)) → Values.Gamma (M := M)}
    (hf : FullGammaFunction B f) (hg : FullGammaFunction B g) :
    FullGammaFunction B (fun z => f z * g z) := by
  let F : Fin 3 → ((α ⊕ Fin 1) → Values.Gamma (M := M)) → Values.Gamma (M := M) :=
    ![fun z => f (z ∘ Sum.inl),fun z => g (z ∘ Sum.inl),fun z => z (.inr 0)]
  have hF : ∀ i, FullGammaFunction B (F i) := by
    intro i
    fin_cases i
    · exact hf.reindex Sum.inl
    · exact hg.reindex Sum.inl
    · exact proj B (Sum.inr 0 : α ⊕ Fin 1)
  exact substitute (FullGammaSyntax.mul_definable B (0 : Fin 3) 1 2) F hF

theorem inv {f : (α → Values.Gamma (M := M)) → Values.Gamma (M := M)}
    (hf : FullGammaFunction B f) : FullGammaFunction B (fun z => (f z)⁻¹) := by
  let F : Fin 3 → ((α ⊕ Fin 1) → Values.Gamma (M := M)) → Values.Gamma (M := M) :=
    ![fun z => f (z ∘ Sum.inl),fun z => z (.inr 0),fun _ => 1]
  have hF : ∀ i, FullGammaFunction B (F i) := by
    intro i
    fin_cases i
    · exact hf.reindex Sum.inl
    · exact proj B (Sum.inr 0 : α ⊕ Fin 1)
    · exact one B
  apply (substitute (FullGammaSyntax.mul_definable B (0 : Fin 3) 1 2) F hF).congr
  intro z
  change (f (z ∘ Sum.inl) * z (.inr 0) = 1) ↔ (f (z ∘ Sum.inl))⁻¹ = z (.inr 0)
  constructor
  · intro h
    apply mul_left_cancel (a := f (z ∘ Sum.inl))
    rw [mul_inv_cancel]
    exact h.symm
  · intro h
    rw [← h]
    exact mul_inv_cancel _

theorem pow {f : (α → Values.Gamma (M := M)) → Values.Gamma (M := M)}
    (hf : FullGammaFunction B f) (k : ℕ) : FullGammaFunction B (fun z => f z ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using one (α := α) B
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem zpow {f : (α → Values.Gamma (M := M)) → Values.Gamma (M := M)}
    (hf : FullGammaFunction B f) (k : ℤ) : FullGammaFunction B (fun z => f z ^ k) := by
  cases k with
  | ofNat k => simpa only [FullGammaFunction,Int.ofNat_eq_natCast,zpow_natCast] using hf.pow k
  | negSucc k => simpa only [zpow_negSucc] using (hf.pow (k+1)).inv

theorem prod {τ : Type} (t : Finset τ)
    (f : τ → (α → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : ∀ i ∈ t, FullGammaFunction B (f i)) :
    FullGammaFunction B (fun z => ∏ i ∈ t, f i z) := by
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using one (α := α) B
  | @insert i t hit ih =>
    have hi := hf i (Finset.mem_insert_self i t)
    have ht := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hit] using hi.mul ht

theorem eq {f g : (α → Values.Gamma (M := M)) → Values.Gamma (M := M)}
    (hf : FullGammaFunction B f) (hg : FullGammaFunction B g) :
    FullGammaSyntax.Definable B (fun z => f z = g z) := by
  let F : Fin 2 → (α → Values.Gamma (M := M)) → Values.Gamma (M := M) := ![f,g]
  have hF : ∀ i, FullGammaFunction B (F i) := by intro i; fin_cases i; exact hf; exact hg
  exact substitute (FullGammaSyntax.eq_definable B (0 : Fin 2) 1) F hF
end FullGammaFunction
end DiamondIntegral.Section3
