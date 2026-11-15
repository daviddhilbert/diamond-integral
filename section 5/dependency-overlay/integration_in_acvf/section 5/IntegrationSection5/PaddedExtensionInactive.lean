import IntegrationSection5.PaddedUnaryBranchExtension
import IntegrationSection5.RelativeLabelPreservation
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5.PaddedUnaryBranchExtension
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b} {H : DefSet (M := M) S 1 l}
variable {u : SpecialBijection A B} {ρ : Fin a → Fin l} {E : Set (Fin a → RV (M := M))} {previous : Option Bool}

theorem inactive_sameRV (C : PaddedUnaryBranchExtension (G := G) u H ρ E previous)
    (p q : H) (hp : p.val.2 ∘ ρ ∉ E) (hq : q.val.2 ∘ ρ ∉ E) (he : SameRV p.val q.val) :
    SameRV (C.map p).val (C.map q).val := by
  have hFlag (p : H) (hp : p.val.2 ∘ ρ ∉ E) : (C.preMap p).val.2 ∘ (Fin.natAdd 1 ∘ ρ) ∉ E := by
    rw [C.prefix_formula]
    have hl := congrArg (fun s => s ∘ ρ) (coordinateCanonical_oldRV 0 p.val)
    exact hl.symm ▸ hp
  apply C.lift.inactive_sameRV (C.preMap p) (C.preMap q) (hFlag p hp) (hFlag q hq)
  rw [C.prefix_formula,C.prefix_formula]
  exact coordinateCanonical_sameRV 0 he

theorem oldLabels (C : PaddedUnaryBranchExtension (G := G) u H ρ E previous) (p : H) :
    (C.map p).val.2 ∘ suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget C.special)) = p.val.2 := by
  funext j
  exact specialRelative_oldLabels (specialRelativeBoundary_forget C.special) p j

end IntegrationInACVF.Section5.PaddedUnaryBranchExtension

namespace IntegrationInACVF.Section5.PaddedUnaryBranchExtension
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b} {H : DefSet (M := M) S 1 l}
variable {u : SpecialBijection A B} {ρ : Fin a → Fin l} {E : Set (Fin a → RV (M := M))} {previous : Option Bool}

theorem prefix_oldLabels (C : PaddedUnaryBranchExtension (G := G) u H ρ E previous) (p : H) :
    (C.preMap p).val.2 ∘ (Fin.natAdd 1 ∘ ρ) = p.val.2 ∘ ρ := by
  rw [C.prefix_formula]
  exact congrArg (fun s => s ∘ ρ) (coordinateCanonical_oldRV 0 p.val)

theorem active_image_whole (C : PaddedUnaryBranchExtension (G := G) u H ρ E previous) :
    carrier C.lift.active_image = {q | ∃ p : H, p.val.2 ∘ ρ ∈ E ∧ (C.map p).val = q} := by
  rw [C.lift.active_image_eq]
  ext q
  constructor
  · rintro ⟨p,hp,hpq⟩
    obtain ⟨a,rfl⟩ := (specialRelative_bijective (specialRelativeBoundary_forget C.prefix_special)).2 p
    rw [C.prefix_oldLabels] at hp
    exact ⟨a,hp,hpq⟩
  · rintro ⟨p,hp,hpq⟩
    refine ⟨C.preMap p,?_,hpq⟩
    rwa [C.prefix_oldLabels]

theorem active_slice (C : PaddedUnaryBranchExtension (G := G) u H ρ E previous) :
    carrier C.lift.active_image = {q | q ∈ carrier C.lift.target ∧
      q.2 ∘ (suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget C.special)) ∘ ρ) ∈ E} := by
  rw [C.active_image_whole]
  ext q
  constructor
  · rintro ⟨p,hp,rfl⟩
    refine ⟨(C.map p).property,?_⟩
    change ((C.map p).val.2 ∘ suffixIndex _) ∘ ρ ∈ E
    rwa [C.oldLabels]
  · rintro ⟨hq,he⟩
    obtain ⟨p,hp⟩ := (specialRelative_bijective (specialRelativeBoundary_forget C.special)).2 ⟨q,hq⟩
    have hval := congrArg (fun z : C.lift.target => z.val) hp
    refine ⟨p,?_,hval⟩
    have hl := congrArg (fun s => s ∘ ρ) (C.oldLabels p)
    change (C.map p).val.2 ∘ (suffixIndex _ ∘ ρ) = p.val.2 ∘ ρ at hl
    rw [← hl,hval]
    exact he

end IntegrationInACVF.Section5.PaddedUnaryBranchExtension
