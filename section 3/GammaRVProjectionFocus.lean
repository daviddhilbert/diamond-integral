import IntegrationSection5.GammaActiveUnaryFocus
import Section5.CoordinateLift

/-! RV coordinate projection extends an existing focus while retaining
every VF coordinate and the original Gamma graph. These are presentation
adapters for lifting an already constructed base preparation to a family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m l : ℕ}

def gammaRVProjection (ρ : Fin m → Fin l) (p : Point (M := M) n l) : Point (M := M) n m :=
  (p.1,p.2 ∘ ρ)

theorem gammaRVProjection_replace (ρ : Fin m → Fin l) (j : Fin n)
    (p : Point (M := M) n l) (x : VF (M := M)) :
    gammaRVProjection ρ (replace j p x) = replace j (gammaRVProjection ρ p) x := rfl

theorem gammaRVProjection_sameRV (ρ : Fin m → Fin l) {p q : Point (M := M) n l}
    (h : SameRV p q) : SameRV (gammaRVProjection ρ p) (gammaRVProjection ρ q) := by
  obtain ⟨hv,ht⟩ := (sameRV_iff _ _).mp h
  exact (sameRV_iff _ _).mpr ⟨hv,congrArg (fun t => t ∘ ρ) ht⟩

def gammaRVProjectionMap (ρ : Fin m → Fin l)
    (H : SpecialTransformations.Section5.DefSet (M := M) S n l) :
    Map H (PresentedSet.univ (pointSpace n m) S) :=
  Map.ofCodes H (gammaRVProjection ρ)
    (fun z => Sum.elim (fun i => z (.inl i)) (fun j => z (.inr (ρ j))))
    (by intro i; cases i <;> exact rawProj S _)
    (by intro c; exact ⟨c.property.1,fun j => c.property.2 (ρ j)⟩)
    (by intro c; rfl)

theorem gammaRVProjection_preimage_definable (ρ : Fin m → Fin l)
    (D : Set (Point (M := M) n m)) (hD : SetDefinable (pointSpace n m) S D) :
    SetDefinable (pointSpace n l) S {p | gammaRVProjection ρ p ∈ D} := by
  let f := gammaRVProjectionMap ρ (PresentedSet.univ (pointSpace (M := M) n l) S)
  have h := Map.definable_preimage f hD
  convert h using 1
  ext p
  exact ⟨fun hp => ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩,fun ⟨a,ha,hp⟩ => ha ▸ hp⟩

theorem gammaRVProjection_preimage_gamma (ρ : Fin m → Fin l)
    (D : Set (Point (M := M) n m)) (hD : GammaSetDefinable B D) :
    GammaSetDefinable B {p | gammaRVProjection ρ p ∈ D} := by
  let f := gammaRVProjectionMap ρ (PresentedSet.univ (pointSpace (M := M) n l) B.real)
  have h := (gammaLogicInput B).preimage_real f hD
  convert h using 1
  ext p
  exact ⟨fun hp => ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩,fun ⟨a,ha,hp⟩ => ha ▸ hp⟩

variable {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
variable {H : SpecialTransformations.Section5.DefSet (M := M) S n l} {j : Fin n} {k : Fin m}

def gammaRVProjectionFocusGeometry (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, gammaRVProjection ρ p ∈ carrier A) : FocusGeometry (carrier H) j (ρ k) where
  tagged p hp := D.tagged (gammaRVProjection ρ p) (hHA p hp)
  locus := {p | gammaRVProjection ρ p ∈ D.locus} ∩ hull (carrier H)
  locus_pullback := isRVPullback_inter ((isRVPullback_iff _).mpr (by
    intro p hp q he
    exact (isRVPullback_iff _).mp D.locus_pullback _ hp _ (gammaRVProjection_sameRV ρ he))) (hull_idem _)
  locus_subset := Set.inter_subset_right
  center p := D.center (gammaRVProjection ρ p)
  independent p hp q hq he := by
    apply D.independent (gammaRVProjection ρ p) ⟨hHA p hp.1,hp.2.1⟩
      (gammaRVProjection ρ q) ⟨hHA q hq.1,hq.2.1⟩
    exact congrArg (gammaRVProjection ρ) he
  center_mem := by
    intro p hp
    have hm := D.center_mem (gammaRVProjection ρ p) ⟨hHA p hp.1,hp.2.1⟩
    have hr := D.toFocusGeometry.center_sameRV (gammaRVProjection ρ p) ⟨hHA p hp.1,hp.2.1⟩
    exact ⟨hm,p,hp.1,sameRV_replace j p _ hr⟩

def gammaRVProjectionFocusActive (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, gammaRVProjection ρ p ∈ carrier A) :
    SpecialTransformations.Section5.DefSet (M := M) S n l :=
  PresentedSet.mk (carrier H ∩ (gammaRVProjectionFocusGeometry D ρ hHA).locus)
    (SetDefinable.inter _ (setDefinable H) (SetDefinable.inter _
      (gammaRVProjection_preimage_definable ρ D.locus D.locus_definable) (hull_definable H)))

def gammaRVProjectionFocusActiveMap (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, gammaRVProjection ρ p ∈ carrier A) :
    Map (gammaRVProjectionFocusActive D ρ hHA) D.active :=
  Map.mk (fun p => ⟨gammaRVProjection ρ p.val,hHA _ p.property.1,p.property.2.1⟩)
    (Map.graph_definable (gammaRVProjectionMap ρ (gammaRVProjectionFocusActive D ρ hHA)))

def gammaRVProjectionFocus (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, gammaRVProjection ρ p ∈ carrier A) : Focus H j (ρ k) where
  toFocusGeometry := gammaRVProjectionFocusGeometry D ρ hHA
  locus_definable := SetDefinable.inter _
    (gammaRVProjection_preimage_definable ρ D.locus D.locus_definable) (hull_definable H)
  center_graph := by
    have h := Map.graph_definable (Map.comp D.centerMap (gammaRVProjectionFocusActiveMap D ρ hHA))
    apply RelationDefinable.congr _ _ h
    intro p z
    constructor
    · rintro ⟨a,rfl,hz⟩
      exact ⟨a.property,(congrFun hz 0).symm⟩
    · rintro ⟨hp,hz⟩
      refine ⟨⟨p,hp⟩,rfl,?_⟩
      funext i
      fin_cases i
      exact hz.symm

theorem gammaRVProjectionFocus_eta (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, gammaRVProjection ρ p ∈ carrier A)
    (p : Point (M := M) n l) (hp : p ∈ carrier H) :
    gammaRVProjection ρ ((gammaRVProjectionFocus D ρ hHA).toFocusGeometry.eta p) =
      D.toFocusGeometry.eta (gammaRVProjection ρ p) := by
  have hh := subset_hull (carrier H) hp
  by_cases hd : gammaRVProjection ρ p ∈ D.locus <;>
    simp [FocusGeometry.eta,gammaRVProjectionFocus,gammaRVProjectionFocusGeometry,hd,hh,
      gammaRVProjection_replace] <;> rfl

theorem gammaRVProjectionFocus_gamma (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, gammaRVProjection ρ p ∈ carrier A)
    (hH : GammaSetDefinable B (carrier H)) (hD : GammaFocusDefinable B D) :
    GammaFocusDefinable B (gammaRVProjectionFocus D ρ hHA) := by
  let L := gammaLogicInput B
  refine ⟨L.inter (gammaRVProjection_preimage_gamma ρ D.locus hD.1) (L.hull hH),?_⟩
  let f := gammaRVProjectionMap ρ (PresentedSet.univ (pointSpace (M := M) n l) B.real)
  have h := L.restrict_graph hH (L.comp_graph (L.real_map_graph f) hD.2)
  apply GammaGraphDefinable.congr h
  intro p z
  constructor
  · rintro ⟨hp,q,⟨a,ha,hq⟩,hqA,hz⟩
    have he : q = gammaRVProjection ρ p := hq.symm.trans (congrArg (gammaRVProjection ρ) ha)
    rw [he] at hqA hz
    exact ⟨⟨hp,hqA.2,subset_hull _ hp⟩,hz⟩
  · rintro ⟨⟨hp,hd,hh⟩,hz⟩
    exact ⟨hp,gammaRVProjection ρ p,⟨⟨p,Set.mem_univ _⟩,rfl,rfl⟩,⟨hHA p hp,hd⟩,hz⟩

def gammaRVCanonicalProjection (ρ : Fin m → Fin l) : Fin (n+m) → Fin (n+l) :=
  Fin.addCases (Fin.castAdd l) (fun i => Fin.natAdd n (ρ i))

theorem gammaRVProjection_canonical (ρ : Fin m → Fin l) (p : Point (M := M) n l) :
    gammaRVProjection (gammaRVCanonicalProjection ρ) (canonical p) = canonical (gammaRVProjection ρ p) := by
  refine Prod.ext rfl ?_
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [gammaRVProjection,gammaRVCanonicalProjection,canonical]

end DiamondIntegral.Section3
