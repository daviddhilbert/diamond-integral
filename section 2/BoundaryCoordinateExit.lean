import «section 2».ScalarBoundary
import «section 2».RectangleImages

/-! Coordinate-exit witnesses for the approved RV-boundary induction.
Every VF coordinate keeps its RV tag and every auxiliary RV label stays
fixed. An exit cannot occur in a singleton-zero coordinate. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A partially met RV-polydisc has an exit in one coordinate while all
its RV tags and auxiliary labels are retained. -/
theorem rvBoundary_coordinate_exit {n m : ℕ} (A : Set (Mixed M n m))
    (t : Fin n → RVInfinity M) (s : Fin m → RVInfinity M)
    (ht : (t, s) ∈ rvBoundary A) :
    ∃ c : Fin n → VF M, (c, s) ∈ A ∧ tupleRV M c = t ∧
      ∃ i x, rv M x = t i ∧ (Function.update c i x, s) ∉ A ∧ t i ≠ rvZero M := by
  classical
  obtain ⟨⟨p, hp, hpt⟩, q, hq, hqt⟩ := ht
  have hpRV : tupleRV M p.1 = t := congrArg Prod.fst hpt
  have hqRV : tupleRV M q.1 = t := congrArg Prod.fst hqt
  have hps : p.2 = s := congrArg Prod.snd hpt
  have hqs : q.2 = s := congrArg Prod.snd hqt
  change q ∉ A at hq
  let D : Fin n → Set (VF M) := fun i => {x | rv M x = t i}
  have hpD : ∀ i, p.1 i ∈ D i := fun i => congrFun hpRV i
  have hqD : ∀ i, q.1 i ∈ D i := fun i => congrFun hqRV i
  have hpA : p.1 ∈ vfFibre A s := by simpa only [vfFibre, Set.mem_ofPred_eq, ← hps] using hp
  have hqA : q.1 ∉ vfFibre A s := by simpa only [vfFibre, Set.mem_ofPred_eq, ← hqs] using hq
  obtain ⟨c, hcD, hcA, i, x, hxD, hxA⟩ :=
    rectangle_coordinate_exit D (vfFibre A s) p.1 q.1 hpD hqD hpA hqA
  have hcRV : tupleRV M c = t := funext hcD
  refine ⟨c, hcA, hcRV, i, x, hxD, hxA, ?_⟩
  intro hzero
  have hc0 : c i = 0 := (rv_eq_zero_iff _).mp ((hcD i).trans hzero)
  have hx0 : x = 0 := (rv_eq_zero_iff _).mp (hxD.trans hzero)
  have he : Function.update c i x = c := by
    rw [← hc0] at hx0
    rw [hx0, Function.update_eq_self]
  exact hxA (he.symm ▸ hcA)

/-- The scalar coordinate section retains the fixed other coordinates
and the original auxiliary labels in its membership condition. -/
def vfCoordinateSection {n m : ℕ} (A : Set (Mixed M n m))
    (s : Fin m → RVInfinity M) (c : Fin n → VF M) (i : Fin n) : Set M :=
  {z | ∃ x : VF M, x.val = z ∧ (Function.update c i x, s) ∈ A}

/-- Every boundary tuple has a unary-section boundary witness with the
same output coordinate tag, including on zero-coordinate faces. -/
theorem rvBoundary_coordinate_section {n m : ℕ} (A : Set (Mixed M n m))
    (t : Fin n → RVInfinity M) (s : Fin m → RVInfinity M)
    (ht : (t, s) ∈ rvBoundary A) :
    ∃ c : Fin n → VF M, (c, s) ∈ A ∧ tupleRV M c = t ∧
      ∃ i, t i ∈ scalarRVBoundary (vfCoordinateSection A s c i) ∧ t i ≠ rvZero M := by
  classical
  obtain ⟨c, hcA, hcRV, i, x, hxRV, hxA, hne⟩ := rvBoundary_coordinate_exit A t s ht
  refine ⟨c, hcA, hcRV, i, ?_, hne⟩
  constructor
  · refine ⟨c i, ?_, congrFun hcRV i⟩
    refine ⟨c i, rfl, ?_⟩
    simpa only [Function.update_eq_self] using hcA
  · refine ⟨x, ?_, hxRV⟩
    rintro ⟨y, hy, hyA⟩
    have he : y = x := Subtype.ext hy
    subst y
    exact hxA hyA

end DiamondIntegral.Section2
