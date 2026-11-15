import IntegrationSection5.RelativeSpecial
import IntegrationSection5.GammaCoordinateFibres

/-! A definable centre inside the actual source RV class produces the actual
hull focus and its original-Gamma certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}

def hullTranslationFocus (hTag : Tagged (carrier A) i k)
    (c : Point (M := M) n m → VF (M := M))
    (hind : ∀ p ∈ carrier A, ∀ q ∈ carrier A, erase i p = erase i q → c p = c q)
    (hRV : ∀ p ∈ carrier A, rv (c p) = rv (vfAt p i))
    (hc : RelationDefinable (pointSpace n m) (SpecialTransformations.Section4.vfSpace 1) S
      (fun p z => p ∈ carrier A ∧ z 0 = c p)) : Focus A i k where
  tagged := hTag
  locus := hull (carrier A)
  locus_pullback := hull_idem _
  locus_subset := Set.Subset.refl _
  center := c
  independent := fun p hp q hq he => hind p hp.1 q hq.1 he
  center_mem := fun p hp => ⟨p,hp.1,sameRV_replace i p (c p) (hRV p hp.1)⟩
  locus_definable := hull_definable A
  center_graph := RelationDefinable.congr _ _ hc (by
    intro p z
    constructor
    · rintro ⟨hp,hz⟩
      exact ⟨⟨hp,subset_hull _ hp⟩,hz⟩
    · rintro ⟨hp,hz⟩
      exact ⟨hp.1,hz⟩)

theorem hullTranslationFocus_apply (hTag : Tagged (carrier A) i k)
    (c : Point (M := M) n m → VF (M := M))
    (hind : ∀ p ∈ carrier A, ∀ q ∈ carrier A, erase i p = erase i q → c p = c q)
    (hRV : ∀ p ∈ carrier A, rv (c p) = rv (vfAt p i))
    (hc : RelationDefinable (pointSpace n m) (SpecialTransformations.Section4.vfSpace 1) S
      (fun p z => p ∈ carrier A ∧ z 0 = c p)) (a : A) :
    ((hullTranslationFocus hTag c hind hRV hc).etaMap a).val =
      replace i a.val (vfAt a.val i-c a.val) := by
  change (if a.val ∈ hull (carrier A) then _ else _) = _
  rw [if_pos (subset_hull _ a.property)]
  rfl

theorem hullTranslationFocus_gamma {G : GammaParameters.Base (M := M)}
    (hA : GammaSetDefinable G (carrier A)) (hTag : Tagged (carrier A) i k)
    (c : Point (M := M) n m → VF (M := M))
    (hind : ∀ p ∈ carrier A, ∀ q ∈ carrier A, erase i p = erase i q → c p = c q)
    (hRV : ∀ p ∈ carrier A, rv (c p) = rv (vfAt p i))
    (hc : RelationDefinable (pointSpace n m) (SpecialTransformations.Section4.vfSpace 1) S
      (fun p z => p ∈ carrier A ∧ z 0 = c p))
    (hcG : GammaScalarGraphDefinable G (fun p x => p ∈ carrier A ∧ x = c p)) :
    GammaFocusDefinable G (hullTranslationFocus hTag c hind hRV hc) := by
  refine ⟨(gammaLogicInput G).hull hA,?_⟩
  change GammaScalarGraphDefinable G (fun p x => p ∈ carrier A ∩ hull (carrier A) ∧ x = c p)
  apply GammaScalarGraphDefinable.congr hcG
  intro p x
  constructor
  · rintro ⟨hp,hx⟩
    exact ⟨⟨hp,subset_hull _ hp⟩,hx⟩
  · rintro ⟨hp,hx⟩
    exact ⟨hp.1,hx⟩

end IntegrationInACVF.Section5
