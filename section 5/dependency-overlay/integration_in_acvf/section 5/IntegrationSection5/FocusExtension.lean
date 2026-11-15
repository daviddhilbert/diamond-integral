import IntegrationSection5.GammaFocusSection
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5.Focus
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A H : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}

def extendGeometry (D : SpecialTransformations.Section5.Focus A i k)
    (kH : Fin m) (hTag : Tagged (carrier H) i kH)
    (hActive : ∀ p ∈ carrier H, p ∈ D.locus → p ∈ carrier A) :
    FocusGeometry (carrier H) i kH where
  tagged := hTag
  locus := D.locus ∩ hull (carrier H)
  locus_pullback := isRVPullback_inter D.locus_pullback (hull_idem _)
  locus_subset := Set.inter_subset_right
  center := D.center
  independent p hp q hq he := D.independent p ⟨hActive p hp.1 hp.2.1,hp.2.1⟩
    q ⟨hActive q hq.1 hq.2.1,hq.2.1⟩ he
  center_mem p hp :=
    ⟨D.center_mem p ⟨hActive p hp.1 hp.2.1,hp.2.1⟩,
      p,hp.1,sameRV_replace i p _ (D.toFocusGeometry.center_sameRV p ⟨hActive p hp.1 hp.2.1,hp.2.1⟩)⟩

def extendActive (D : SpecialTransformations.Section5.Focus A i k)
    (kH : Fin m) (hTag : Tagged (carrier H) i kH)
    (hActive : ∀ p ∈ carrier H, p ∈ D.locus → p ∈ carrier A) : DefSet (M := M) S n m :=
  PresentedSet.mk (carrier H ∩ (extendGeometry D kH hTag hActive).locus)
    (SetDefinable.inter _ (setDefinable H) (SetDefinable.inter _ D.locus_definable (hull_definable H)))

def extendActiveMap (D : SpecialTransformations.Section5.Focus A i k)
    (kH : Fin m) (hTag : Tagged (carrier H) i kH)
    (hActive : ∀ p ∈ carrier H, p ∈ D.locus → p ∈ carrier A) :
    Map (extendActive D kH hTag hActive) D.active :=
  Map.inclusion (fun p hp => ⟨hActive p hp.1 hp.2.1,hp.2.1⟩)

def extend (D : SpecialTransformations.Section5.Focus A i k)
    (kH : Fin m) (hTag : Tagged (carrier H) i kH)
    (hActive : ∀ p ∈ carrier H, p ∈ D.locus → p ∈ carrier A) :
    SpecialTransformations.Section5.Focus H i kH where
  toFocusGeometry := extendGeometry D kH hTag hActive
  locus_definable := SetDefinable.inter _ D.locus_definable (hull_definable H)
  center_graph := by
    have h := Map.graph_definable (Map.comp D.centerMap (extendActiveMap D kH hTag hActive))
    apply RelationDefinable.congr _ _ h
    intro p z
    constructor
    · rintro ⟨a,rfl,hz⟩
      exact ⟨a.property,(congrFun hz 0).symm⟩
    · rintro ⟨hp,hz⟩
      refine ⟨⟨p,hp⟩,rfl,?_⟩
      funext j; fin_cases j; exact hz.symm

theorem extend_eta (D : SpecialTransformations.Section5.Focus A i k)
    (kH : Fin m) (hTag : Tagged (carrier H) i kH)
    (hActive : ∀ p ∈ carrier H, p ∈ D.locus → p ∈ carrier A)
    (p : Point (M := M) n m) (hp : p ∈ carrier H) :
    (extend D kH hTag hActive).toFocusGeometry.eta p = D.toFocusGeometry.eta p := by
  have hh := subset_hull (carrier H) hp
  by_cases hd : p ∈ D.locus
  · simp only [FocusGeometry.eta,show p ∈ (extend D kH hTag hActive).locus from ⟨hd,hh⟩,hd,ite_true]
    rfl
  · have hnot : p ∉ (extend D kH hTag hActive).locus := fun h => hd h.1
    simp only [FocusGeometry.eta,ite_eq_right_iff,ite_eq_left_iff]
    rw [if_neg hnot,if_neg hd]

theorem extend_gamma {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
    (D : SpecialTransformations.Section5.Focus A i k)
    (kH : Fin m) (hTag : Tagged (carrier H) i kH)
    (hActive : ∀ p ∈ carrier H, p ∈ D.locus → p ∈ carrier A)
    (hH : GammaSetDefinable G (carrier H)) (hD : GammaFocusDefinable G D) :
    GammaFocusDefinable G (extend D kH hTag hActive) := by
  have hL := (gammaLogicInput G).inter hD.1 ((gammaLogicInput G).hull hH)
  refine ⟨hL,?_⟩
  have h := (gammaLogicInput G).restrict_graph ((gammaLogicInput G).inter hH hL) hD.2
  apply GammaGraphDefinable.congr h
  intro p q
  change ((p ∈ carrier H ∧ p ∈ D.locus ∧ p ∈ hull (carrier H)) ∧
      (p ∈ carrier A ∧ p ∈ D.locus) ∧ vfAt q 0 = D.center p) ↔
    ((p ∈ carrier H ∧ p ∈ D.locus ∧ p ∈ hull (carrier H)) ∧ vfAt q 0 = D.center p)
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,⟨hActive p h.1.1 h.1.2.1,h.1.2.1⟩,h.2⟩⟩

end IntegrationInACVF.Section5.Focus
