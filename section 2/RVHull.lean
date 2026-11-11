import «section 2».Conventions

set_option backward.isDefEq.respectTransparency false

/-! §2.1, `defn:disc`, R022: RV saturation includes every zero fibre and fixes
the existing RV tags. These are set-theoretic results for all finite arities;
they do not assert finiteness of RV fibres after taking a hull (see R170). -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

def rvHull (A : Set (Mixed M n m)) : Set (Mixed M n m) :=
  rvCoordinates M ⁻¹' (rvCoordinates M '' A)

def IsRVPullback (A : Set (Mixed M n m)) : Prop := rvHull A = A

/-- Codes of RV-polydiscs meeting both the set and its complement. -/
def rvBoundary (A : Set (Mixed M n m)) :=
  rvCoordinates M '' A ∩ rvCoordinates M '' Aᶜ

theorem mem_rvHull_iff (A : Set (Mixed M n m)) (p : Mixed M n m) :
    p ∈ rvHull A ↔ ∃ q ∈ A, tupleRV M q.1 = tupleRV M p.1 ∧ q.2 = p.2 := by
  simp only [rvHull, Set.mem_preimage, Set.mem_image, rvCoordinates, Prod.mk.injEq]

theorem subset_rvHull (A : Set (Mixed M n m)) : A ⊆ rvHull A :=
  fun p hp => ⟨p, hp, rfl⟩

theorem rvHull_mono {A B : Set (Mixed M n m)} (h : A ⊆ B) : rvHull A ⊆ rvHull B := by
  rintro p ⟨q, hq, he⟩
  exact ⟨q, h hq, he⟩

@[simp] theorem rvHull_idempotent (A : Set (Mixed M n m)) : rvHull (rvHull A) = rvHull A := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, ⟨a, ha, haq⟩, hqp⟩
    exact ⟨a, ha, haq.trans hqp⟩
  · exact subset_rvHull _

/-- The hull is the least union of whole RV-polydiscs containing the set. -/
theorem rvHull_least {A B : Set (Mixed M n m)} (hAB : A ⊆ B) (hB : IsRVPullback B) :
    rvHull A ⊆ B := by
  rw [← hB]
  exact rvHull_mono hAB

theorem rvHull_preserves_tags (A : Set (Mixed M n m)) :
    Prod.snd '' rvHull A = Prod.snd '' A := by
  apply Set.Subset.antisymm
  · rintro t ⟨p, hp, rfl⟩
    obtain ⟨q, hq, _, he⟩ := (mem_rvHull_iff A p).mp hp
    exact ⟨q, hq, he⟩
  · exact Set.image_mono (subset_rvHull A)

theorem vfFibre_rvHull (A : Set (Mixed M n m)) (t : Fin m → RVInfinity M) :
    vfFibre (rvHull A) t = tupleRV M ⁻¹' (tupleRV M '' vfFibre A t) := by
  ext a
  constructor
  · intro h
    obtain ⟨q, hq, he, ht⟩ := (mem_rvHull_iff A (a, t)).mp h
    refine ⟨q.1, ?_, he⟩
    change (q.1, t) ∈ A
    change q.2 = t at ht
    rw [← ht]
    exact hq
  · rintro ⟨b, hb, he⟩
    exact (mem_rvHull_iff A (a, t)).mpr ⟨(b, t), hb, he, rfl⟩

/-- Coordinate hyperplanes are covered: the all-zero RV-polydisc is a point. -/
@[simp] theorem rvHull_zero_singleton (t : Fin m → RVInfinity M) :
    rvHull ({((fun _ : Fin n => (0 : VF M)), t)} : Set (Mixed M n m)) =
      {((fun _ : Fin n => (0 : VF M)), t)} := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨q, hq, he, ht⟩ := (mem_rvHull_iff _ p).mp hp
    subst q
    have hp0 : p.1 = fun _ => 0 := by
      funext i
      apply (rv_eq_zero_iff (p.1 i)).mp
      have hi := congrFun he i
      simpa [tupleRV] using hi.symm
    exact Prod.ext hp0 ht.symm
  · exact subset_rvHull _

theorem isRVPullback_iff_boundary_empty (A : Set (Mixed M n m)) :
    IsRVPullback A ↔ rvBoundary A = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro c ⟨⟨p, hp, hpc⟩, q, hq, hqc⟩
    have hh : q ∈ rvHull A := ⟨p, hp, hpc.trans hqc.symm⟩
    rw [h] at hh
    exact hq hh
  · intro h
    apply Set.Subset.antisymm _ (subset_rvHull A)
    intro p hp
    by_contra hn
    have hb : rvCoordinates M p ∈ rvBoundary A := ⟨hp, p, hn, rfl⟩
    rw [h] at hb
    exact hb

end DiamondIntegral.Section2
