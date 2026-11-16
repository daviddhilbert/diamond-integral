import «section 6».Covariance
import «section 2».RVHull

/-! The geometric content of R099. The same finite radius works for the
RV-hull, including coordinates with RV-zero. Existing tags are retained.
Definability of the set and of its radii is a separate model-theoretic
requirement; the geometry here does not enlarge the parameter base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

@[simp] theorem value_zero : vfValue (0 : VF M) = Values.infinity :=
  (vfValue_eq_infinity_iff _).mpr rfl

theorem rv_eq_of_value_close {a b : VF M} (hb : b ≠ 0)
    (hclose : vfValue b < vfValue (a - b)) : rv M a = rv M b := by
  apply Subtype.ext
  change iRv a.val = iRv b.val
  rw [CanonicalRV.encoded_eq_iff_close a.property b.property
    (fun h => hb (Subtype.ext h))]
  change ¬ VFValued.predV b (a - b)
  rw [Values.vf_pred_iff_gamma_le]
  exact not_le.mpr hclose

theorem rv_eq_of_close_at_radius {a b : VF M} (γ : Gamma M)
    (hb : vfValue b ≤ γ.val) (hclose : γ.val < vfValue (a - b)) : rv M a = rv M b := by
  have hb0 : b ≠ 0 := by
    intro hz
    have hzero : Values.infinity ≤ γ.val := by simpa only [hz,value_zero] using hb
    exact γ.property (le_antisymm (Values.le_infinity _) hzero)
  exact rv_eq_of_value_close hb0 (hb.trans_lt hclose)

theorem AlphaInvariant.rvSaturation {α : Fin n → Gamma M}
    {A : Set (Fin n → VF M)} (hA : AlphaInvariant α A) :
    AlphaInvariant α (tupleRV M ⁻¹' (tupleRV M '' A)) := by
  classical
  have step (x y : Fin n → VF M) (hxy : Congruent α x y)
      (hx : x ∈ tupleRV M ⁻¹' (tupleRV M '' A)) :
      y ∈ tupleRV M ⁻¹' (tupleRV M '' A) := by
    obtain ⟨a, ha, harv⟩ := hx
    let b : Fin n → VF M := fun i => if (α i).val < vfValue (x i) then y i else a i
    have hax (i : Fin n) : vfValue (a i) = vfValue (x i) :=
      congrArg Values.vrv (congrFun harv i)
    have hab : Congruent α a b := by
      intro i
      by_cases hi : (α i).val < vfValue (x i)
      · have haabove : (α i).val < vfValue (a i) := by rw [hax i]; exact hi
        have haxnear : (α i).val < vfValue (a i - x i) :=
          (lt_min haabove hi).trans_le (vfValue_min_le_sub (a i) (x i))
        have h := vfValue_min_le_sub (a i - x i) (y i - x i)
        rw [show a i - x i - (y i - x i) = a i - y i by abel] at h
        simpa only [b, ite_eq_left hi, valueHom_eq_value] using
          (lt_min haxnear (hxy.symm i)).trans_le h
      · simpa only [b, ite_eq_right hi, sub_self, valueHom_eq_value] using
          gamma_lt_value_zero (α i)
    refine ⟨b, (hA a b hab).mp ha, ?_⟩
    funext i
    by_cases hi : (α i).val < vfValue (x i)
    · simp only [tupleRV, b, ite_eq_left hi]
    · have hxval : vfValue (x i) ≤ (α i).val := le_of_not_gt hi
      have hx0 : x i ≠ 0 := by
        intro hz
        have hzero : (α i).val < vfValue (x i) := by
          simpa only [hz, valueHom_eq_value] using gamma_lt_value_zero (α i)
        exact hzero.not_ge hxval
      have hryx : rv M (y i) = rv M (x i) :=
        rv_eq_of_value_close hx0 (hxval.trans_lt (hxy.symm i))
      simpa only [tupleRV, b, ite_eq_right hi] using (congrFun harv i).trans hryx.symm
  intro x y hxy
  exact ⟨step x y hxy, step y x hxy.symm⟩

def VFBounded (A : Set (Mixed M n m)) : Prop :=
  ∃ γ : Gamma M, ∀ p ∈ A, ∀ i, γ.val ≤ vfValue (p.1 i)

def RVSupportDoublyBounded (A : Set (Mixed M n m)) : Prop :=
  ∃ γ : Gamma M, ∀ p ∈ A, ∀ i,
    (γ⁻¹).val ≤ Values.vrv (p.2 i) ∧ Values.vrv (p.2 i) ≤ γ.val

/-- Geometric part of Definition 6.2 only. Original-base definability of
the set and fiber radii must still be supplied in a definable adapter. -/
structure ProperInvariantGeometry (A : Set (Mixed M n m)) : Prop where
  vfBounded : VFBounded A
  rvBounded : RVSupportDoublyBounded A
  fibers : ∀ t : Fin m → RVInfinity M, ∃ α : Fin n → Gamma M,
    AlphaInvariant α (vfFibre A t)

theorem VFBounded.mono {A B : Set (Mixed M n m)}
    (hA : VFBounded A) (hBA : B ⊆ A) : VFBounded B := by
  obtain ⟨γ,hγ⟩ := hA
  exact ⟨γ,fun p hp i => hγ p (hBA hp) i⟩

theorem RVSupportDoublyBounded.mono {A B : Set (Mixed M n m)}
    (hA : RVSupportDoublyBounded A) (hBA : B ⊆ A) : RVSupportDoublyBounded B := by
  obtain ⟨γ,hγ⟩ := hA
  exact ⟨γ,fun p hp i => hγ p (hBA hp) i⟩

theorem VFBounded.rvHull {A : Set (Mixed M n m)} (hA : VFBounded A) :
    VFBounded (rvHull A) := by
  obtain ⟨γ,hγ⟩ := hA
  refine ⟨γ,fun p hp i => ?_⟩
  obtain ⟨q,hq,hrv,_⟩ := (mem_rvHull_iff A p).mp hp
  have he : vfValue (q.1 i) = vfValue (p.1 i) := congrArg Values.vrv (congrFun hrv i)
  rw [← he]
  exact hγ q hq i

theorem RVSupportDoublyBounded.rvHull {A : Set (Mixed M n m)}
    (hA : RVSupportDoublyBounded A) : RVSupportDoublyBounded (rvHull A) := by
  obtain ⟨γ,hγ⟩ := hA
  refine ⟨γ,fun p hp i => ?_⟩
  obtain ⟨q,hq,_,htags⟩ := (mem_rvHull_iff A p).mp hp
  rw [← htags]
  exact hγ q hq i

theorem ProperInvariantGeometry.rvHull {A : Set (Mixed M n m)}
    (hA : ProperInvariantGeometry A) : ProperInvariantGeometry (rvHull A) := by
  refine ⟨hA.vfBounded.rvHull,hA.rvBounded.rvHull,fun t => ?_⟩
  obtain ⟨α,hα⟩ := hA.fibers t
  refine ⟨α,?_⟩
  rw [vfFibre_rvHull]
  exact hα.rvSaturation

theorem ProperInvariantGeometry.inter {A B : Set (Mixed M n m)}
    (hA : ProperInvariantGeometry A) (hB : ProperInvariantGeometry B) :
    ProperInvariantGeometry (A ∩ B) := by
  refine ⟨hA.vfBounded.mono Set.inter_subset_left,
    hA.rvBounded.mono Set.inter_subset_left,fun t => ?_⟩
  obtain ⟨α,hα⟩ := hA.fibers t
  obtain ⟨β,hβ⟩ := hB.fibers t
  exact ⟨fun i => max (α i) (β i),hα.inter hβ⟩

theorem ProperInvariantGeometry.diff {A B : Set (Mixed M n m)}
    (hA : ProperInvariantGeometry A) (hB : ProperInvariantGeometry B) :
    ProperInvariantGeometry (A \ B) := by
  refine ⟨hA.vfBounded.mono Set.sdiff_subset,
    hA.rvBounded.mono Set.sdiff_subset,fun t => ?_⟩
  obtain ⟨α,hα⟩ := hA.fibers t
  obtain ⟨β,hβ⟩ := hB.fibers t
  exact ⟨fun i => max (α i) (β i),hα.diff hβ⟩

theorem ProperInvariantGeometry.hull_complement {A : Set (Mixed M n m)}
    (hA : ProperInvariantGeometry A) : ProperInvariantGeometry (DiamondIntegral.Section2.rvHull A \ A) :=
  hA.rvHull.diff hA

end DiamondIntegral.Section6
