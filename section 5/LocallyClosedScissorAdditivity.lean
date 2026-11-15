import Mathlib.Topology.LocallyClosed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

/-! Closed/open scissors imply additivity for every finite disjoint
locally closed partition. Admissibility records an optional invariance
condition and is retained throughout the proof. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical Set Topology

structure LocallyClosedScissorFunction (X R : Type*) [TopologicalSpace X] [AddCommGroup R] where
  admissible : Set X → Prop
  empty_admissible : admissible ∅
  inter_admissible : ∀ {S T}, admissible S → admissible T → admissible (S ∩ T)
  sdiff_admissible : ∀ {S T}, admissible S → admissible T → admissible (S \ T)
  closure_admissible : ∀ {S}, admissible S → admissible (closure S)
  value : Set X → R
  empty : value ∅ = 0
  split : ∀ S Z, IsLocallyClosed S → admissible S → IsClosed Z → admissible Z →
    value S = value (S ∩ Z) + value (S \ Z)

theorem finite_locallyClosed_scissor_partition {X R ι : Type*}
    [TopologicalSpace X] [AddCommGroup R] [DecidableEq ι]
    (F : LocallyClosedScissorFunction X R) (s : Finset ι)
    (S : Set X) (D : ι → Set X) (hS : IsLocallyClosed S) (hSi : F.admissible S)
    (hD : ∀ i ∈ s, IsLocallyClosed (D i)) (hiD : ∀ i ∈ s, F.admissible (D i))
    (hsub : ∀ i ∈ s, D i ⊆ S)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (D i) (D j))
    (hcov : ∀ x ∈ S, ∃ i ∈ s, x ∈ D i) : F.value S = ∑ i ∈ s, F.value (D i) := by
  induction s using Finset.induction_on generalizing S D with
  | empty =>
    have he : S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i, hi, _⟩ := hcov x hx
      simpa using hi
    simp [he, F.empty]
  | @insert i s his ih =>
    have hDi := hD i (Finset.mem_insert_self i s)
    have hiDi := hiD i (Finset.mem_insert_self i s)
    have hDiS := hsub i (Finset.mem_insert_self i s)
    let Z := closure (D i)
    let K := Z \ D i
    have hZ : IsClosed Z := isClosed_closure
    have hiZ : F.admissible Z := F.closure_admissible hiDi
    have hK : IsClosed K := by
      simpa only [coborder, compl_compl] using hDi.isOpen_coborder.isClosed_compl
    have hiK : F.admissible K := F.sdiff_admissible hiZ hiDi
    have hother (j : ι) (hj : j ∈ s) : Disjoint (D j) (D i) :=
      hdisj j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i s)
        (by intro he; exact his (he ▸ hj))
    have hsub' (j : ι) (hj : j ∈ s) := hsub j (Finset.mem_insert_of_mem hj)
    have hcovK : ∀ x ∈ S ∩ K, ∃ j ∈ s, x ∈ D j ∩ Z := by
      intro x hx
      obtain ⟨j, hj, hxj⟩ := hcov x hx.1
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact False.elim (hx.2.2 hxj)
      · exact ⟨j, hj, hxj, hx.2.1⟩
    have hcovU : ∀ x ∈ S \ Z, ∃ j ∈ s, x ∈ D j \ Z := by
      intro x hx
      obtain ⟨j, hj, hxj⟩ := hcov x hx.1
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact False.elim (hx.2 (subset_closure hxj))
      · exact ⟨j, hj, hxj, hx.2⟩
    have hsumK : F.value (S ∩ K) = ∑ j ∈ s, F.value (D j ∩ Z) :=
      ih (S ∩ K) (fun j => D j ∩ Z) (hS.inter hK.isLocallyClosed)
        (F.inter_admissible hSi hiK)
        (fun j hj => (hD j (Finset.mem_insert_of_mem hj)).inter hZ.isLocallyClosed)
        (fun j hj => F.inter_admissible (hiD j (Finset.mem_insert_of_mem hj)) hiZ)
        (by
          intro j hj x hx
          exact ⟨hsub' j hj hx.1, hx.2, fun hxi => Set.disjoint_left.mp (hother j hj) hx.1 hxi⟩)
        (by
          intro j hj k hk hne
          exact (hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne).mono
            Set.inter_subset_left Set.inter_subset_left)
        hcovK
    have hsumU : F.value (S \ Z) = ∑ j ∈ s, F.value (D j \ Z) :=
      ih (S \ Z) (fun j => D j \ Z) (hS.inter hZ.isOpen_compl.isLocallyClosed)
        (F.sdiff_admissible hSi hiZ)
        (fun j hj => (hD j (Finset.mem_insert_of_mem hj)).inter hZ.isOpen_compl.isLocallyClosed)
        (fun j hj => F.sdiff_admissible (hiD j (Finset.mem_insert_of_mem hj)) hiZ)
        (fun j hj x hx => ⟨hsub' j hj hx.1, hx.2⟩)
        (by
          intro j hj k hk hne
          exact (hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne).mono
            Set.sdiff_subset Set.sdiff_subset)
        hcovU
    have heK : (S ∩ Z) ∩ K = S ∩ K := by
      ext x
      exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, hx.2.1⟩, hx.2⟩⟩
    have heD : (S ∩ Z) \ K = D i := by
      ext x
      constructor
      · intro hx
        by_contra hn
        exact hx.2 ⟨hx.1.2, hn⟩
      · intro hx
        exact ⟨⟨hDiS hx, subset_closure hx⟩, fun hk => hk.2 hx⟩
    have hsZ := F.split S Z hS hSi hZ hiZ
    have hsK := F.split (S ∩ Z) K (hS.inter hZ.isLocallyClosed)
      (F.inter_admissible hSi hiZ) hK hiK
    rw [heK, heD, hsumK] at hsK
    rw [hsZ, hsK, hsumU, Finset.sum_insert his]
    have heSum : (∑ j ∈ s, F.value (D j ∩ Z)) + (∑ j ∈ s, F.value (D j \ Z)) =
        ∑ j ∈ s, F.value (D j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      exact (F.split (D j) Z (hD j (Finset.mem_insert_of_mem hj))
        (hiD j (Finset.mem_insert_of_mem hj)) hZ hiZ).symm
    calc
      ((∑ j ∈ s, F.value (D j ∩ Z)) + F.value (D i)) + (∑ j ∈ s, F.value (D j \ Z)) =
          F.value (D i) + ((∑ j ∈ s, F.value (D j ∩ Z)) + (∑ j ∈ s, F.value (D j \ Z))) := by
        abel
      _ = _ := by rw [heSum]

end DiamondIntegral.Section5
