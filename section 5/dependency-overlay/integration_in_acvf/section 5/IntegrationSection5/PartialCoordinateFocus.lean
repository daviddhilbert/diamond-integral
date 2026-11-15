import IntegrationSection5.ActiveUnaryProjection
import IntegrationSection5.GammaFocusSection
import Section5.GammaLiftRelation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}
namespace Focus
variable {A : DefSet (M := M) S 1 m} {H : DefSet (M := M) S n l}
variable {k : Fin m}

def partialCoordinateLiftGeometry (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin m → Fin l)
    (kH : Fin l) (hTag : Tagged (carrier H) i kH)
    (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ D.locus →
      activeUnaryProjection i ρ p ∈ carrier A) :
    FocusGeometry (carrier H) i kH where
  tagged := hTag
  locus := {p | activeUnaryProjection i ρ p ∈ D.locus} ∩ hull (carrier H)
  locus_pullback := isRVPullback_inter ((isRVPullback_iff _).mpr (by
    intro p hp q he
    exact (isRVPullback_iff _).mp D.locus_pullback _ hp _ (activeUnaryProjection_sameRV i ρ he))) (hull_idem _)
  locus_subset := Set.inter_subset_right
  center p := D.center (activeUnaryProjection i ρ p)
  independent p hp q hq he := by
    apply D.independent (activeUnaryProjection i ρ p) ⟨hHA p hp.1 hp.2.1,hp.2.1⟩
      (activeUnaryProjection i ρ q) ⟨hHA q hq.1 hq.2.1,hq.2.1⟩
    have h := congrArg (activeUnaryProjection i ρ) he
    simpa only [erase,activeUnaryProjection_replace] using h
  center_mem := by
    intro p hp
    have hlow := D.center_mem (activeUnaryProjection i ρ p) ⟨hHA p hp.1 hp.2.1,hp.2.1⟩
    have hr := D.toFocusGeometry.center_sameRV (activeUnaryProjection i ρ p) ⟨hHA p hp.1 hp.2.1,hp.2.1⟩
    refine ⟨?_,p,hp.1,sameRV_replace i p _ hr⟩
    change activeUnaryProjection i ρ (replace i p (D.center (activeUnaryProjection i ρ p))) ∈ D.locus
    rwa [activeUnaryProjection_replace]

def partialCoordinateLiftActive (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin m → Fin l)
    (kH : Fin l) (hTag : Tagged (carrier H) i kH)
    (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ D.locus →
      activeUnaryProjection i ρ p ∈ carrier A) : DefSet (M := M) S n l :=
  PresentedSet.mk (carrier H ∩ (partialCoordinateLiftGeometry D i ρ kH hTag hHA).locus)
    (SetDefinable.inter _ (setDefinable H)
      (SetDefinable.inter _ (activeUnaryProjection_preimage i ρ D.locus D.locus_definable) (hull_definable H)))

def partialCoordinateLiftActiveMap (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin m → Fin l)
    (kH : Fin l) (hTag : Tagged (carrier H) i kH)
    (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ D.locus →
      activeUnaryProjection i ρ p ∈ carrier A) :
    Map (partialCoordinateLiftActive D i ρ kH hTag hHA) D.active :=
  Map.mk (fun p => ⟨activeUnaryProjection i ρ p.val,hHA _ p.property.1 p.property.2.1,p.property.2.1⟩)
    (Map.graph_definable (activeUnaryProjectionMap i ρ (partialCoordinateLiftActive D i ρ kH hTag hHA)))

def partialCoordinateLift (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin m → Fin l)
    (kH : Fin l) (hTag : Tagged (carrier H) i kH)
    (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ D.locus →
      activeUnaryProjection i ρ p ∈ carrier A) :
    SpecialTransformations.Section5.Focus H i kH where
  toFocusGeometry := partialCoordinateLiftGeometry D i ρ kH hTag hHA
  locus_definable := SetDefinable.inter _
    (activeUnaryProjection_preimage i ρ D.locus D.locus_definable) (hull_definable H)
  center_graph := by
    have h := Map.graph_definable (Map.comp D.centerMap (partialCoordinateLiftActiveMap D i ρ kH hTag hHA))
    apply RelationDefinable.congr _ _ h
    intro p z
    constructor
    · rintro ⟨a,rfl,hz⟩
      exact ⟨a.property,(congrFun hz 0).symm⟩
    · rintro ⟨hp,hz⟩
      refine ⟨⟨p,hp⟩,rfl,?_⟩
      funext j
      fin_cases j
      exact hz.symm

theorem partialCoordinateLift_eta (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin m → Fin l)
    (kH : Fin l) (hTag : Tagged (carrier H) i kH)
    (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ D.locus →
      activeUnaryProjection i ρ p ∈ carrier A)
    (p : Point (M := M) n l) (hp : p ∈ carrier H) :
    activeUnaryProjection i ρ ((partialCoordinateLift D i ρ kH hTag hHA).toFocusGeometry.eta p) =
      D.toFocusGeometry.eta (activeUnaryProjection i ρ p) := by
  have hh := subset_hull (carrier H) hp
  by_cases hd : activeUnaryProjection i ρ p ∈ D.locus
  · have hl : p ∈ (partialCoordinateLift D i ρ kH hTag hHA).locus := ⟨hd,hh⟩
    simp only [FocusGeometry.eta,if_pos hl,if_pos hd]
    exact activeUnaryProjection_replace i ρ p _
  · have hl : p ∉ (partialCoordinateLift D i ρ kH hTag hHA).locus := fun h => hd h.1
    simp only [FocusGeometry.eta,if_neg hl,if_neg hd]


theorem partialCoordinateLift_inactive (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin m → Fin l)
    (kH : Fin l) (hTag : Tagged (carrier H) i kH)
    (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ D.locus →
      activeUnaryProjection i ρ p ∈ carrier A)
    (p : Point (M := M) n l) (hp : activeUnaryProjection i ρ p ∉ D.locus) :
    (partialCoordinateLift D i ρ kH hTag hHA).toFocusGeometry.eta p = p := by
  exact if_neg (fun h => hp h.1)

theorem partialCoordinateLift_gamma {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
    (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin m → Fin l)
    (kH : Fin l) (hTag : Tagged (carrier H) i kH)
    (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ D.locus →
      activeUnaryProjection i ρ p ∈ carrier A)
    (hH : GammaSetDefinable G (carrier H)) (hD : GammaFocusDefinable G D) :
    GammaFocusDefinable G (partialCoordinateLift D i ρ kH hTag hHA) := by
  let U := PresentedSet.univ (pointSpace (M := M) n l) G.real
  let F := activeUnaryProjectionMap i ρ U
  let I := Map.id (PresentedSet.univ (pointSpace (M := M) 1 0) G.real)
  have hPre : GammaSetDefinable G {p | activeUnaryProjection i ρ p ∈ D.locus} := by
    convert (gammaLogicInput G).preimage_real F hD.1 using 1
    ext p
    exact ⟨fun h => ⟨⟨p,Set.mem_univ _⟩,rfl,h⟩,fun ⟨a,ha,h⟩ => ha ▸ h⟩
  have hL := (gammaLogicInput G).inter hPre ((gammaLogicInput G).hull hH)
  refine ⟨hL,?_⟩
  have h := (gammaLogicInput G).restrict_graph ((gammaLogicInput G).inter hH hL)
    (hD.2.preimage_maps F I)
  apply GammaGraphDefinable.congr h
  intro p q
  change ((p ∈ carrier H ∧ activeUnaryProjection i ρ p ∈ D.locus ∧ p ∈ hull (carrier H)) ∧
      (activeUnaryProjection i ρ p ∈ carrier A ∧ activeUnaryProjection i ρ p ∈ D.locus) ∧
        vfAt q 0 = D.center (activeUnaryProjection i ρ p)) ↔
    ((p ∈ carrier H ∧ activeUnaryProjection i ρ p ∈ D.locus ∧ p ∈ hull (carrier H)) ∧
      vfAt q 0 = D.center (activeUnaryProjection i ρ p))
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,⟨hHA p h.1.1 h.1.2.1,h.1.2.1⟩,h.2⟩⟩

end Focus
end IntegrationInACVF.Section5
