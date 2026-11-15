import IntegrationSection5.FibreFocusMaps

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n N m l : ℕ}

def vfRVProjection (ι : Fin n → Fin N) (ρ : Fin m → Fin l) (p : Point (M := M) N l) : Point (M := M) n m :=
  (p.1 ∘ ι,p.2 ∘ ρ)

def vfRVProjectionMap (ι : Fin n → Fin N) (ρ : Fin m → Fin l) (H : DefSet (M := M) S N l) :
    Map H (PresentedSet.univ (pointSpace n m) S) :=
  Map.ofCodes H (vfRVProjection ι ρ) (fun z => Sum.elim (fun j => z (.inl (ι j))) (fun j => z (.inr (ρ j))))
    (fun j => by cases j <;> exact rawProj S _)
    (fun c => ⟨fun j => c.property.1 (ι j),fun j => c.property.2 (ρ j)⟩) (fun _ => rfl)

theorem vfRVProjection_replace (ι : Fin n → Fin N) (hι : Function.Injective ι) (ρ : Fin m → Fin l)
    (i : Fin n) (p : Point (M := M) N l) (x : VF (M := M)) :
    vfRVProjection ι ρ (replace (ι i) p x) = replace i (vfRVProjection ι ρ p) x := by
  refine Prod.ext ?_ rfl
  funext j
  by_cases hj : j = i
  · subst j
    simp [vfRVProjection,replace]
  · have hji : ι j ≠ ι i := fun he => hj (hι he)
    simp [vfRVProjection,replace,hj,hji]

theorem vfRVProjection_sameRV (ι : Fin n → Fin N) (ρ : Fin m → Fin l)
    {p q : Point (M := M) N l} (h : SameRV p q) : SameRV (vfRVProjection ι ρ p) (vfRVProjection ι ρ q) := by
  obtain ⟨hv,hr⟩ := (sameRV_iff _ _).mp h
  exact (sameRV_iff _ _).mpr ⟨fun j => hv (ι j),congrArg (fun v => v ∘ ρ) hr⟩

theorem vfRVProjection_preimage_definable (ι : Fin n → Fin N) (ρ : Fin m → Fin l)
    (D : Set (Point (M := M) n m)) (hD : SetDefinable (pointSpace n m) S D) :
    SetDefinable (pointSpace N l) S {p | vfRVProjection ι ρ p ∈ D} := by
  have h := Map.definable_preimage (vfRVProjectionMap ι ρ (PresentedSet.univ (pointSpace N l) S)) hD
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩
  · rintro ⟨a,ha,hD⟩
    exact ha ▸ hD

namespace FibreFocusData
variable {A : DefSet (M := M) S n m} {H : DefSet (M := M) S N l} {i : Fin n} {k : Fin m}

def projectionActive (D : FibreFocusData A i k) (ι : Fin n → Fin N) (ρ : Fin m → Fin l) : DefSet (M := M) S N l :=
  PresentedSet.mk (carrier H ∩ {p | vfRVProjection ι ρ p ∈ D.locus})
    (SetDefinable.inter _ (setDefinable H) (vfRVProjection_preimage_definable ι ρ D.locus D.locus_definable))

def projectionActiveMap (D : FibreFocusData A i k) (ι : Fin n → Fin N) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, vfRVProjection ι ρ p ∈ carrier A) : Map (D.projectionActive (H := H) ι ρ) D.active :=
  Map.mk (fun p => ⟨vfRVProjection ι ρ p.val,hHA _ p.property.1,p.property.2⟩)
    (Map.graph_definable (vfRVProjectionMap ι ρ _))

def projectionPullback (D : FibreFocusData A i k) (ι : Fin n → Fin N) (hι : Function.Injective ι) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, vfRVProjection ι ρ p ∈ carrier A) : FibreFocusData H (ι i) (ρ k) where
  tagged p hp := D.tagged _ (hHA p hp)
  locus := {p | vfRVProjection ι ρ p ∈ D.locus}
  locus_definable := vfRVProjection_preimage_definable ι ρ D.locus D.locus_definable
  center p := D.center (vfRVProjection ι ρ p)
  center_graph := by
    have h := Map.graph_definable (Map.comp D.centerMap (D.projectionActiveMap ι ρ hHA))
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
  independent p hp q hq he := by
    apply D.independent _ ⟨hHA p hp.1,hp.2⟩ _ ⟨hHA q hq.1,hq.2⟩
    have h := congrArg (vfRVProjection ι ρ) he
    simpa only [erase,vfRVProjection_replace ι hι] using h
  center_sameRV p hp := D.center_sameRV _ ⟨hHA p hp.1,hp.2⟩
  locus_saturated p hp q hq hs ho :=
    D.locus_saturated _ (hHA p hp) _ (hHA q hq) (vfRVProjection_sameRV ι ρ hs)
      (fun j hj => ho (ι j) (fun he => hj (hι he)))

theorem projectionPullback_eta (D : FibreFocusData A i k) (ι : Fin n → Fin N) (hι : Function.Injective ι)
    (ρ : Fin m → Fin l) (hHA : ∀ p ∈ carrier H, vfRVProjection ι ρ p ∈ carrier A)
    (p : Point (M := M) N l) :
    vfRVProjection ι ρ ((D.projectionPullback ι hι ρ hHA).eta p) = D.eta (vfRVProjection ι ρ p) := by
  by_cases hp : vfRVProjection ι ρ p ∈ D.locus
  · simp only [eta,projectionPullback,Set.mem_setOf_eq,if_pos hp,vfRVProjection_replace ι hι]
    rfl
  · simp only [eta,projectionPullback,Set.mem_setOf_eq,if_neg hp]

end FibreFocusData
end IntegrationInACVF.Section5
