import IntegrationSection5.Corollary58

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
variable {S : Set M} {n m l : ℕ}

def fullRVProjection (ρ : Fin m → Fin l) (p : Point (M := M) n l) : Point (M := M) n m := (p.1,p.2 ∘ ρ)

def fullRVProjectionMap (ρ : Fin m → Fin l) (A : DefSet (M := M) S n l) :
    Map A (PresentedSet.univ (pointSpace n m) S) :=
  Map.ofCodes A (fullRVProjection ρ) (fun z => Sum.elim (z ∘ Sum.inl) (fun j => z (.inr (ρ j))))
    (fun j => by cases j <;> exact rawProj S _)
    (fun c => ⟨c.property.1,fun j => c.property.2 (ρ j)⟩) (fun _ => rfl)

theorem fullRVProjection_erase (ρ : Fin m → Fin l) (i : Fin n) (p : Point (M := M) n l) :
    fullRVProjection ρ (erase i p) = erase i (fullRVProjection ρ p) := rfl

theorem fullRVProjection_replace (ρ : Fin m → Fin l) (i : Fin n) (p : Point (M := M) n l) (x : VF (M := M)) :
    fullRVProjection ρ (replace i p x) = replace i (fullRVProjection ρ p) x := rfl

structure FibreFocusData (A : DefSet (M := M) S n m) (i : Fin n) (k : Fin m) where
  tagged : Tagged (carrier A) i k
  locus : Set (Point (M := M) n m)
  locus_definable : SetDefinable (pointSpace n m) S locus
  center : Point (M := M) n m → VF (M := M)
  center_graph : RelationDefinable (pointSpace n m) (SpecialTransformations.Section4.vfSpace 1) S
    (fun p z => p ∈ carrier A ∩ locus ∧ z 0 = center p)
  independent : ∀ p ∈ carrier A ∩ locus, ∀ q ∈ carrier A ∩ locus, erase i p = erase i q → center p = center q
  center_sameRV : ∀ p ∈ carrier A ∩ locus, rv (center p) = rv (vfAt p i)
  locus_saturated : ∀ p ∈ carrier A, ∀ q ∈ carrier A, SameRV p q →
    (∀ j, j ≠ i → vfAt p j = vfAt q j) → (p ∈ locus ↔ q ∈ locus)

namespace FibreFocusData
variable {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}

def active (D : FibreFocusData A i k) : DefSet (M := M) S n m :=
  PresentedSet.mk (carrier A ∩ D.locus) (SetDefinable.inter _ (setDefinable A) D.locus_definable)

def centerMap (D : FibreFocusData A i k) : Map D.active (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) :=
  Map.mk (fun p => ⟨![D.center p.val],Set.mem_univ _⟩) (RelationDefinable.congr _ _ D.center_graph (by
    intro p z
    constructor
    · rintro ⟨hp,hz⟩
      exact ⟨⟨p,hp⟩,rfl,funext (fun j => by fin_cases j; exact hz.symm)⟩
    · rintro ⟨p,rfl,hz⟩
      exact ⟨p.property,(congrFun hz 0).symm⟩))

def eta (D : FibreFocusData A i k) (p : Point (M := M) n m) : Point (M := M) n m :=
  if p ∈ D.locus then replace i p (vfAt p i-D.center p) else p

variable {H : DefSet (M := M) S n l}
def presentationGeometry (D : FibreFocusData A i k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, fullRVProjection ρ p ∈ carrier A)
    (E : Set (Fin l → RV (M := M)))
    (hFlag : ∀ p ∈ carrier H, p.2 ∈ E ↔ fullRVProjection ρ p ∈ D.locus) :
    FocusGeometry (carrier H) i (ρ k) where
  tagged p hp := D.tagged _ (hHA p hp)
  locus := {p | p.2 ∈ E} ∩ hull (carrier H)
  locus_pullback := isRVPullback_inter ((isRVPullback_iff _).mpr (by
    intro p hp q he
    change q.2 ∈ E
    rw [← ((sameRV_iff _ _).mp he).2]
    exact hp)) (hull_idem _)
  locus_subset := Set.inter_subset_right
  center p := D.center (fullRVProjection ρ p)
  independent p hp q hq he := by
    apply D.independent _ ⟨hHA p hp.1,(hFlag p hp.1).mp hp.2.1⟩ _ ⟨hHA q hq.1,(hFlag q hq.1).mp hq.2.1⟩
    have h := congrArg (fullRVProjection ρ) he
    simpa only [fullRVProjection_erase] using h
  center_mem p hp := by
    have hr := D.center_sameRV _ ⟨hHA p hp.1,(hFlag p hp.1).mp hp.2.1⟩
    exact ⟨hp.2.1,p,hp.1,sameRV_replace i p _ hr⟩

def presentationActiveMap (D : FibreFocusData A i k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, fullRVProjection ρ p ∈ carrier A)
    (E : Set (Fin l → RV (M := M)))
    (hE : SetDefinable (pointSpace n l) S {p | p.2 ∈ E})
    (hFlag : ∀ p ∈ carrier H, p.2 ∈ E ↔ fullRVProjection ρ p ∈ D.locus) :
    Map (PresentedSet.mk (carrier H ∩ (D.presentationGeometry ρ hHA E hFlag).locus)
      (SetDefinable.inter _ (setDefinable H) (SetDefinable.inter _ hE (hull_definable H)))) D.active :=
  Map.mk (fun p => ⟨fullRVProjection ρ p.val,hHA _ p.property.1,(hFlag _ p.property.1).mp p.property.2.1⟩)
    (Map.graph_definable (fullRVProjectionMap ρ _))

def presentationFocus (D : FibreFocusData A i k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, fullRVProjection ρ p ∈ carrier A)
    (E : Set (Fin l → RV (M := M)))
    (hE : SetDefinable (pointSpace n l) S {p | p.2 ∈ E})
    (hFlag : ∀ p ∈ carrier H, p.2 ∈ E ↔ fullRVProjection ρ p ∈ D.locus) : Focus H i (ρ k) where
  toFocusGeometry := D.presentationGeometry ρ hHA E hFlag
  locus_definable := SetDefinable.inter _ hE (hull_definable H)
  center_graph := by
    have h := Map.graph_definable (Map.comp D.centerMap (D.presentationActiveMap ρ hHA E hE hFlag))
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

theorem presentationFocus_eta (D : FibreFocusData A i k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, fullRVProjection ρ p ∈ carrier A)
    (E : Set (Fin l → RV (M := M))) (hE : SetDefinable (pointSpace n l) S {p | p.2 ∈ E})
    (hFlag : ∀ p ∈ carrier H, p.2 ∈ E ↔ fullRVProjection ρ p ∈ D.locus)
    (p : H) : fullRVProjection ρ ((D.presentationFocus ρ hHA E hE hFlag).toFocusGeometry.eta p.val) = D.eta (fullRVProjection ρ p.val) := by
  have hHull := subset_hull (carrier H) p.property
  by_cases he : p.val.2 ∈ E
  · have ha : fullRVProjection ρ p.val ∈ D.locus := (hFlag _ p.property).mp he
    have hg : p.val ∈ (D.presentationFocus ρ hHA E hE hFlag).locus := ⟨he,hHull⟩
    simp only [FocusGeometry.eta,if_pos hg,eta,if_pos ha,fullRVProjection_replace]
    rfl
  · have ha : fullRVProjection ρ p.val ∉ D.locus := fun h => he ((hFlag _ p.property).mpr h)
    have hg : p.val ∉ (D.presentationFocus ρ hHA E hE hFlag).locus := fun h => he h.1
    simp only [FocusGeometry.eta,if_neg hg,eta,if_neg ha]

end FibreFocusData
end IntegrationInACVF.Section5
