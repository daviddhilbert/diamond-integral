import IntegrationSection5.CentripetalRelativeBoundary
import IntegrationSection5.GammaCoordinateCanonical

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

def activeUnaryProjection (i : Fin n) (ρ : Fin m → Fin l) (p : Point (M := M) n l) :
    Point (M := M) 1 m := (fun _ => vfAt p i,p.2 ∘ ρ)

theorem activeUnaryProjection_sameRV (i : Fin n) (ρ : Fin m → Fin l)
    {p q : Point (M := M) n l} (h : SameRV p q) :
    SameRV (activeUnaryProjection i ρ p) (activeUnaryProjection i ρ q) := by
  obtain ⟨hv,hr⟩ := (sameRV_iff p q).mp h
  apply (sameRV_iff _ _).mpr
  exact ⟨fun _ => hv i,congrArg (fun r => r ∘ ρ) hr⟩

theorem activeUnaryProjection_replace (i : Fin n) (ρ : Fin m → Fin l)
    (p : Point (M := M) n l) (x : VF (M := M)) :
    activeUnaryProjection i ρ (replace i p x) = replace 0 (activeUnaryProjection i ρ p) x := by
  refine Prod.ext ?_ rfl
  funext j
  fin_cases j
  simp [activeUnaryProjection,replace,vfAt]

def activeUnaryProjectionMap (i : Fin n) (ρ : Fin m → Fin l) (A : DefSet (M := M) S n l) :
    Map A (PresentedSet.univ (pointSpace 1 m) S) :=
  Map.ofCodes A (activeUnaryProjection i ρ)
    (fun z => Sum.elim (fun _ => z (.inl i)) (fun j => z (.inr (ρ j))))
    (by intro j; cases j <;> exact rawProj S _)
    (by intro c; exact ⟨fun _ => c.property.1 i,fun j => c.property.2 (ρ j)⟩)
    (by intro c; rfl)

theorem activeUnaryProjection_preimage (i : Fin n) (ρ : Fin m → Fin l)
    (D : Set (Point (M := M) 1 m)) (hD : SetDefinable (pointSpace 1 m) S D) :
    SetDefinable (pointSpace n l) S {p | activeUnaryProjection i ρ p ∈ D} := by
  have h := Map.definable_preimage (activeUnaryProjectionMap i ρ
    (PresentedSet.univ (pointSpace n l) S)) hD
  convert h using 1
  ext p
  exact ⟨fun hp => ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩,fun ⟨a,ha,hp⟩ => ha ▸ hp⟩

namespace Focus
variable {A : DefSet (M := M) S 1 m} {H : DefSet (M := M) S n l}
variable {k : Fin m}

def coordinateLiftGeometry (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ carrier A) :
    FocusGeometry (carrier H) i (ρ k) where
  tagged p hp := D.tagged (activeUnaryProjection i ρ p) (hHA p hp)
  locus := {p | activeUnaryProjection i ρ p ∈ D.locus} ∩ hull (carrier H)
  locus_pullback := isRVPullback_inter ((isRVPullback_iff _).mpr (by
    intro p hp q he
    exact (isRVPullback_iff _).mp D.locus_pullback _ hp _ (activeUnaryProjection_sameRV i ρ he))) (hull_idem _)
  locus_subset := Set.inter_subset_right
  center p := D.center (activeUnaryProjection i ρ p)
  independent p hp q hq he := by
    apply D.independent (activeUnaryProjection i ρ p) ⟨hHA p hp.1,hp.2.1⟩
      (activeUnaryProjection i ρ q) ⟨hHA q hq.1,hq.2.1⟩
    have h := congrArg (activeUnaryProjection i ρ) he
    simpa only [erase,activeUnaryProjection_replace] using h
  center_mem := by
    intro p hp
    have hlow := D.center_mem (activeUnaryProjection i ρ p) ⟨hHA p hp.1,hp.2.1⟩
    have hr := D.toFocusGeometry.center_sameRV (activeUnaryProjection i ρ p) ⟨hHA p hp.1,hp.2.1⟩
    refine ⟨?_,p,hp.1,sameRV_replace i p _ hr⟩
    change activeUnaryProjection i ρ (replace i p (D.center (activeUnaryProjection i ρ p))) ∈ D.locus
    rwa [activeUnaryProjection_replace]

def coordinateLiftActive (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ carrier A) : DefSet (M := M) S n l :=
  PresentedSet.mk (carrier H ∩ (coordinateLiftGeometry D i ρ hHA).locus)
    (SetDefinable.inter _ (setDefinable H)
      (SetDefinable.inter _ (activeUnaryProjection_preimage i ρ D.locus D.locus_definable) (hull_definable H)))

def coordinateLiftActiveMap (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ carrier A) :
    Map (coordinateLiftActive D i ρ hHA) D.active :=
  Map.mk (fun p => ⟨activeUnaryProjection i ρ p.val,hHA _ p.property.1,p.property.2.1⟩)
    (Map.graph_definable (activeUnaryProjectionMap i ρ (coordinateLiftActive D i ρ hHA)))

def coordinateLift (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ carrier A) :
    SpecialTransformations.Section5.Focus H i (ρ k) where
  toFocusGeometry := coordinateLiftGeometry D i ρ hHA
  locus_definable := SetDefinable.inter _
    (activeUnaryProjection_preimage i ρ D.locus D.locus_definable) (hull_definable H)
  center_graph := by
    have h := Map.graph_definable (Map.comp D.centerMap (coordinateLiftActiveMap D i ρ hHA))
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

theorem coordinateLift_eta (D : SpecialTransformations.Section5.Focus A 0 k)
    (i : Fin n) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, activeUnaryProjection i ρ p ∈ carrier A)
    (p : Point (M := M) n l) (hp : p ∈ carrier H) :
    activeUnaryProjection i ρ ((coordinateLift D i ρ hHA).toFocusGeometry.eta p) =
      D.toFocusGeometry.eta (activeUnaryProjection i ρ p) := by
  have hh := subset_hull (carrier H) hp
  by_cases hd : activeUnaryProjection i ρ p ∈ D.locus
  · have hl : p ∈ (coordinateLift D i ρ hHA).locus := ⟨hd,hh⟩
    simp only [FocusGeometry.eta,if_pos hl,if_pos hd]
    exact activeUnaryProjection_replace i ρ p _
  · have hl : p ∉ (coordinateLift D i ρ hHA).locus := fun h => hd h.1
    simp only [FocusGeometry.eta,if_neg hl,if_neg hd]

end Focus
end IntegrationInACVF.Section5
