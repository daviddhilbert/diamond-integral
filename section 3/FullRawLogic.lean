import IntegrationSection3ACVF.FullBaseDefinability
import Section3.GammaRVSeparation
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : FullBaseAtomicity.Base (M := M)} {α β : Type} [Finite α] [Finite β]

abbrev FullRawDefinable (B : FullBaseAtomicity.Base (M := M)) {α : Type} (P : (α → M) → Prop) : Prop :=
  FullBaseAtomicity.OverBase B {z | P z}

namespace FullRawDefinable
variable {P Q : (α → M) → Prop}

theorem and (hp : FullRawDefinable B P) (hq : FullRawDefinable B Q) :
    FullRawDefinable B (fun z => P z ∧ Q z) := FullBaseAtomicity.OverBase.inter hp hq

theorem not (hp : FullRawDefinable B P) : FullRawDefinable B (fun z => ¬ P z) :=
  FullBaseAtomicity.OverBase.compl hp

theorem or (hp : FullRawDefinable B P) (hq : FullRawDefinable B Q) :
    FullRawDefinable B (fun z => P z ∨ Q z) := FullBaseAtomicity.OverBase.union hp hq

theorem imp (hp : FullRawDefinable B P) (hq : FullRawDefinable B Q) :
    FullRawDefinable B (fun z => P z → Q z) :=
  FullBaseAtomicity.OverBase.congr (hp.not.or hq) (fun z => by change (¬ P z ∨ Q z) ↔ (P z → Q z); tauto)

theorem iff (hp : FullRawDefinable B P) (hq : FullRawDefinable B Q) :
    FullRawDefinable B (fun z => P z ↔ Q z) :=
  FullBaseAtomicity.OverBase.congr ((hp.imp hq).and (hq.imp hp)) (fun _ => ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩)

theorem reindex (hp : FullRawDefinable B P) (f : α → β) :
    FullRawDefinable B (fun z => P (z ∘ f)) := FullBaseAtomicity.OverBase.preimage_comp hp f

theorem exists_block {R : (α ⊕ β → M) → Prop} (hr : FullRawDefinable B R) :
    FullRawDefinable B (fun z => ∃ u : β → M, R (Sum.elim z u)) :=
  FullBaseAtomicity.OverBase.exists_block hr

theorem forall_block {R : (α ⊕ β → M) → Prop} (hr : FullRawDefinable B R) :
    FullRawDefinable B (fun z => ∀ u : β → M, R (Sum.elim z u)) :=
  FullBaseAtomicity.OverBase.forall_block hr

theorem forall_finite {τ : Type} [Finite τ] {R : τ → (α → M) → Prop}
    (hr : ∀ t, FullRawDefinable B (R t)) : FullRawDefinable B (fun z => ∀ t, R t z) :=
  FullBaseAtomicity.OverBase.forall_finite hr
theorem forall_one {R : (α → M) → M → Prop}
    (hr : FullRawDefinable B (fun z : α ⊕ Fin 1 → M => R (z ∘ Sum.inl) (z (.inr 0)))) :
    FullRawDefinable B (fun z => ∀ v, R z v) := by
  apply FullBaseAtomicity.OverBase.congr hr.forall_block
  intro z
  exact ⟨fun h v => h (fun _ => v),fun h v => h (v 0)⟩

theorem exists_two {R : (α → M) → M → M → Prop}
    (hr : FullRawDefinable B (fun z : α ⊕ Fin 2 → M => R (z ∘ Sum.inl) (z (.inr 0)) (z (.inr 1)))) :
    FullRawDefinable B (fun z => ∃ l u, R z l u) := by
  apply FullBaseAtomicity.OverBase.congr hr.exists_block
  intro z
  exact ⟨fun ⟨v,hv⟩ => ⟨v 0,v 1,hv⟩,fun ⟨l,u,h⟩ => ⟨![l,u],h⟩⟩

end FullRawDefinable

theorem fullRaw_nonzero (B : FullBaseAtomicity.Base (M := M)) (i : α) :
    FullRawDefinable B (fun z : α → M => NonzeroRV (z i)) := by
  let P (z : α → M) := NonzeroRV (z i)
  let S := B.real
  have hd := nonzero_codes_normalized_definable (M := M) S
  have hh : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) α {z | P z} := by
    letI := CanonicalStructure.normalize (M := M)
    exact hd.preimage_comp (fun _ : Fin 1 => i)
  exact FullBaseAtomicity.OverBase.of_real hh

theorem fullRaw_rv (B : FullBaseAtomicity.Base (M := M)) (i : α) :
    FullRawDefinable B (fun z : α → M => iRV (z i)) := by
  let P (z : α → M) := iRV (z i)
  let S := B.real
  have hd := (definableAt_iff_normalized_raw S .rv _).mp (definableAt_sort S .rv) |>.1
  have hh : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) α {z | P z} := by
    letI := CanonicalStructure.normalize (M := M)
    exact hd.preimage_comp (fun _ : Fin 1 => i)
  exact FullBaseAtomicity.OverBase.of_real hh

theorem fullRaw_codeLt (B : FullBaseAtomicity.Base (M := M)) (i j : α) :
    FullRawDefinable B (fun z : α → M => EndpointLogic.codeLt (z i) (z j)) := by
  let P (z : α → M) := EndpointLogic.codeLt (z i) (z j)
  let S := B.real
  have hd := EndpointLogic.codeLt_definable (M := M) S
  have hh : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) α {z | P z} := by
    letI := CanonicalStructure.normalize (M := M)
    exact hd.preimage_comp (![i,j] : Fin 2 → α)
  exact FullBaseAtomicity.OverBase.of_real hh
end DiamondIntegral.Section3
