import IntegrationSection5.PartialCoordinateFocus
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a l : ℕ}

theorem rv_predicate_on_hull {A : DefSet (M := M) S 1 a}
    (C : Set (Fin a → RV (M := M))) (hA : ∀ p ∈ carrier A, p.2 ∈ C)
    (p : Point (M := M) 1 a) (hp : p ∈ hull (carrier A)) : p.2 ∈ C := by
  obtain ⟨q,hq,he⟩ := hp
  have hLabels := ((sameRV_iff _ _).mp he).2
  exact hLabels ▸ hA q hq

namespace Focus
variable {A : DefSet (M := M) S 1 a} {H : DefSet (M := M) S n l} {k : Fin a}

theorem rvPredicate_active_condition (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin a → Fin l) (C : Set (Fin a → RV (M := M)))
    (hA : ∀ p ∈ carrier A, p.2 ∈ C)
    (hHA : ∀ p ∈ carrier H, p.2 ∘ ρ ∈ C → activeUnaryProjection i ρ p ∈ carrier A)
    (p : Point (M := M) n l) (hp : p ∈ carrier H)
    (hl : activeUnaryProjection i ρ p ∈ D.locus) :
    activeUnaryProjection i ρ p ∈ carrier A := by
  exact hHA p hp (rv_predicate_on_hull C hA _ (D.locus_subset hl))

def rvPredicateLift (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin a → Fin l) (C : Set (Fin a → RV (M := M)))
    (hA : ∀ p ∈ carrier A, p.2 ∈ C)
    (hHA : ∀ p ∈ carrier H, p.2 ∘ ρ ∈ C → activeUnaryProjection i ρ p ∈ carrier A)
    (kH : Fin l) (hTag : Tagged (carrier H) i kH) :
    SpecialTransformations.Section5.Focus H i kH :=
  partialCoordinateLift D i ρ kH hTag (rvPredicate_active_condition D i ρ C hA hHA)

theorem rvPredicateLift_projection (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin a → Fin l) (C : Set (Fin a → RV (M := M)))
    (hA : ∀ p ∈ carrier A, p.2 ∈ C)
    (hHA : ∀ p ∈ carrier H, p.2 ∘ ρ ∈ C → activeUnaryProjection i ρ p ∈ carrier A)
    (kH : Fin l) (hTag : Tagged (carrier H) i kH)
    (p : H) :
    activeUnaryProjection i ρ ((rvPredicateLift D i ρ C hA hHA kH hTag).etaMap p).val =
      D.toFocusGeometry.eta (activeUnaryProjection i ρ p.val) :=
  partialCoordinateLift_eta D i ρ kH hTag (rvPredicate_active_condition D i ρ C hA hHA) p.val p.property

theorem rvPredicateLift_inactive (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin a → Fin l) (C : Set (Fin a → RV (M := M)))
    (hA : ∀ p ∈ carrier A, p.2 ∈ C)
    (hHA : ∀ p ∈ carrier H, p.2 ∘ ρ ∈ C → activeUnaryProjection i ρ p ∈ carrier A)
    (kH : Fin l) (hTag : Tagged (carrier H) i kH)
    (p : H) (hp : p.val.2 ∘ ρ ∉ C) :
    ((rvPredicateLift D i ρ C hA hHA kH hTag).etaMap p).val = p.val := by
  apply partialCoordinateLift_inactive
  intro hl
  exact hp (rv_predicate_on_hull C hA _ (D.locus_subset hl))

theorem rvPredicateLift_gamma {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
    (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin a → Fin l) (C : Set (Fin a → RV (M := M)))
    (hA : ∀ p ∈ carrier A, p.2 ∈ C)
    (hHA : ∀ p ∈ carrier H, p.2 ∘ ρ ∈ C → activeUnaryProjection i ρ p ∈ carrier A)
    (kH : Fin l) (hTag : Tagged (carrier H) i kH)
    (hH : GammaSetDefinable G (carrier H)) (hD : GammaFocusDefinable G D) :
    GammaFocusDefinable G (rvPredicateLift D i ρ C hA hHA kH hTag) :=
  partialCoordinateLift_gamma D i ρ kH hTag (rvPredicate_active_condition D i ρ C hA hHA) hH hD

end Focus
end IntegrationInACVF.Section5
