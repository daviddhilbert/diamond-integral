import IntegrationSection5.RVProjectionPadding
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {a m l : ℕ}
variable {AE : DefSet (M := M) S 1 a} {A : DefSet (M := M) S 1 m} {D : DefSet (M := M) S 1 l}

theorem rvclass_of_projection_product (σ : Fin a → Fin m) (Q : Point (M := M) 1 m → Prop)
    (hA : carrier A = {p | activeUnaryProjection 0 σ p ∈ carrier AE ∧ Q p})
    (hAE : ∀ p ∈ carrier AE, ∀ q ∈ carrier AE, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0)) :
    ∀ p ∈ carrier A, ∀ q ∈ carrier A, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) := by
  intro p hp q hq he
  have hpE := ((Set.ext_iff.mp hA p).mp hp).1
  have hqE := ((Set.ext_iff.mp hA q).mp hq).1
  exact hAE _ hpE _ hqE (congrArg (fun s => s ∘ σ) he)

namespace RVProjectionPadding
variable {ρ : Fin m → Fin l}

def refinedPassive (D : DefSet (M := M) S 1 l) (ρ : Fin m → Fin l)
    (Q : Point (M := M) 1 m → Prop) (p : Point (M := M) 1 l) : Prop :=
  Q (activeUnaryProjection 0 ρ p) ∧ p.2 ∈ paddingRVLabels D

theorem refinedPassive_independent (Q : Point (M := M) 1 m → Prop)
    (hQ : ∀ p x, Q (replace 0 p x) ↔ Q p) :
    ∀ p x, refinedPassive D ρ Q (replace 0 p x) ↔ refinedPassive D ρ Q p := by
  intro p x
  change (Q (activeUnaryProjection 0 ρ (replace 0 p x)) ∧ _) ↔ (Q (activeUnaryProjection 0 ρ p) ∧ _)
  rw [activeUnaryProjection_replace,hQ]
  rfl

theorem refined_product_source (P : RVProjectionPadding (G := G) D A ρ)
    (σ : Fin a → Fin m) (Q : Point (M := M) 1 m → Prop)
    (hA : carrier A = {p | activeUnaryProjection 0 σ p ∈ carrier AE ∧ Q p})
    (hAE : ∀ p ∈ carrier AE, ∀ q ∈ carrier AE, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0)) :
    carrier D = {p | activeUnaryProjection 0 (ρ ∘ σ) p ∈ carrier AE ∧ refinedPassive D ρ Q p} := by
  have hD := P.product_source (rvclass_of_projection_product σ Q hA hAE)
  ext p
  constructor
  · intro hp
    obtain ⟨hpA,hPad⟩ := (Set.ext_iff.mp hD p).mp hp
    obtain ⟨hpE,hQ⟩ := (Set.ext_iff.mp hA (activeUnaryProjection 0 ρ p)).mp hpA
    exact ⟨hpE,hQ,hPad⟩
  · rintro ⟨hpE,hQ,hPad⟩
    exact (Set.ext_iff.mp hD p).mpr ⟨(Set.ext_iff.mp hA (activeUnaryProjection 0 ρ p)).mpr ⟨hpE,hQ⟩,hPad⟩

end RVProjectionPadding
end IntegrationInACVF.Section5
