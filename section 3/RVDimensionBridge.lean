import «section 2».RVMapGraphs
import Section4.RVDimension
import Section4.RVCoordinates
import Section4.CodeMaps

/-! The RV-dimension interface in §§2 and 3. Replacing the unique RV zero
by RV one is finite-to-one in the same arity. Consequently allowing zero
target coordinates does not change the least finite-map arity. Graph
conversion retains the original parameter set and every coordinate. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language Set
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m k : ℕ}

def rvSumGraph (A : DefSet (rawRVSpace (M := M) m) S)
    (f : A → Fin k → Section2.RVInfinity M) : Set (Fin m ⊕ Fin k → M) :=
  {z | ∃ a : A, rvValues a.val = z ∘ Sum.inl ∧ rvValues (f a) = z ∘ Sum.inr}

theorem rv_relation_eq_sumGraph (A : DefSet (rawRVSpace (M := M) m) S)
    (f : A → Fin k → Section2.RVInfinity M) :
    (rawRVSpace m).relation (rawRVSpace k)
      (fun x y => ∃ a : A, a.val = x ∧ f a = y) = rvSumGraph A f := by
  ext z
  constructor
  · rintro ⟨hx, hy, a, ha, hb⟩
    exact ⟨a, (congrArg rvValues ha).trans (rvValues_decode ⟨_, hx⟩),
      (congrArg rvValues hb).trans (rvValues_decode ⟨_, hy⟩)⟩
  · rintro ⟨a, ha, hb⟩
    refine ⟨⟨a.val, ha⟩, ⟨f a, hb⟩, a, ?_, ?_⟩
    · exact rvValues_injective (ha.trans
        (rvValues_decode (n := m) ⟨z ∘ Sum.inl, ⟨a.val, ha⟩⟩).symm)
    · exact rvValues_injective (hb.trans
        (rvValues_decode (n := k) ⟨z ∘ Sum.inr, ⟨f a, hb⟩⟩).symm)

theorem rvMapGraph_sumGraph (A : DefSet (rawRVSpace (M := M) m) S)
    (f : A → Fin k → Section2.RV M) :
    Section2.rvMapGraph A.carrier f =
      (fun z : Fin (m+k) → M => z ∘ finSumFinEquiv) ⁻¹'
        rvSumGraph A (fun a i => (f a i).val) := by
  rfl

theorem rvMapGraph_definable_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) m) S) (f : A → Fin k → Section2.RV M) :
    DefinableOver S (fun _ => .rv) (Section2.rvMapGraph A.carrier f) ↔
      (rawRVSpace m).RelationDefinable (rawRVSpace k) S
        (fun x y => ∃ a : A, a.val = x ∧ (fun i => (f a i).val) = y) := by
  have he := rv_relation_eq_sumGraph A (fun a i => (f a i).val)
  constructor
  · intro h
    change S.Definable LRV _
    rw [he]
    have hh := h.raw_definable.preimage_comp
      (finSumFinEquiv.symm : Fin (m+k) → Fin m ⊕ Fin k)
    have hset : (fun z : Fin m ⊕ Fin k → M => z ∘ finSumFinEquiv.symm) ⁻¹'
        Section2.rvMapGraph A.carrier f = rvSumGraph A (fun a i => (f a i).val) := by
      ext z
      simp [Section2.rvMapGraph, rvSumGraph, Function.comp_def,
        Section2.rvInputValues, Section2.rvTargetValues, rvValues]
      rfl
    rw [hset] at hh
    exact hh
  · intro h
    apply raw_definableOver_sorted hc
    · rw [rvMapGraph_sumGraph]
      change S.Definable LRV _ at h
      rw [he] at h
      exact h.preimage_comp (finSumFinEquiv : Fin m ⊕ Fin k → Fin (m+k))
    · exact Section2.rvMapGraph_sorted A.carrier f

def cleanRV (t : Fin k → Section2.RVInfinity M) : Fin k → Section2.RVInfinity M :=
  fun i => ⟨Section2.nonzeroRVCode (t i).val 0,
    (Section2.nonzeroRVCode_proper _ (t i).property 0).1⟩

theorem cleanRV_nonzero (t : Fin k → Section2.RVInfinity M) (i : Fin k) :
    (cleanRV t i).val ≠ iRVZero :=
  (Section2.nonzeroRVCode_proper _ (t i).property 0).2

def cleanRVMap (A : DefSet (rawRVSpace (M := M) k) S) :
    Map A (DefSet.univ (rawRVSpace k) S) :=
  Map.ofCodes A cleanRV (fun z i => Section2.nonzeroRVCode (z i) 0)
    (fun i => Section2.nonzeroRVCode_definable S i 0)
    (fun c => ⟨cleanRV ((rawRVSpace k).decode c), by
      funext i
      exact congrArg (fun x => Section2.nonzeroRVCode x 0) (congrFun (rvValues_decode c) i)⟩)
    (fun c => by
      apply rvValues_injective
      exact (rvValues_decode _).trans (by
        funext i
        exact congrArg (fun x => Section2.nonzeroRVCode x 0) (congrFun (rvValues_decode c) i).symm))

theorem cleanRVMap_finite (A : DefSet (rawRVSpace (M := M) k) S) :
    (cleanRVMap A).FiniteFibres := by
  classical
  intro b
  have hfin := Set.Finite.pi' (fun i : Fin k => Set.toFinite ({Section2.rvZero M, b.val i} :
    Set (Section2.RVInfinity M)))
  apply (hfin.preimage (show Function.Injective (fun a : A => a.val) from Subtype.val_injective).injOn).subset
  intro a ha i
  by_cases hz : (a.val i).val = iRVZero
  · exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext hz))
  · apply Set.mem_insert_iff.mpr
    right
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    have h := congrArg (fun t : DefSet.univ (rawRVSpace (M := M) k) S => (t.val i).val) ha
    simpa only [cleanRVMap, Map.ofCodes_apply, cleanRV, Section2.nonzeroRVCode,
      ite_eq_left (rfl : (0 : Fin 2) = 0), ite_eq_right hz, ite_true] using h

/-- Zero target coordinates may be removed without increasing the target
arity. This is a finite-to-one replacement, not an asserted bijection. -/
theorem rvFiniteMap_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) m) S) (k : ℕ) :
    Section2.RVHasFiniteMap S A.carrier k ↔
      ∃ f : Map A (DefSet.univ (rawRVSpace k) S), f.FiniteFibres := by
  classical
  constructor
  · rintro ⟨f, hf, hg⟩
    let F : Map A (DefSet.univ (rawRVSpace k) S) :=
      ⟨fun a => ⟨fun i => (f a i).val, Set.mem_univ _⟩,
        (rvMapGraph_definable_iff hc A f).mp hg⟩
    refine ⟨F, fun b => ?_⟩
    by_cases hne : ({a : A | F a = b} : Set A).Nonempty
    · obtain ⟨a₀, ha₀⟩ := hne
      apply (hf (f a₀)).subset
      intro a ha
      funext i
      apply Subtype.ext
      exact congrArg (fun z : DefSet.univ (rawRVSpace (M := M) k) S => z.val i)
        (ha.trans ha₀.symm)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact Set.finite_empty
  · rintro ⟨f, hf⟩
    let F := (cleanRVMap (DefSet.univ (rawRVSpace (M := M) k) S)).comp f
    have hF : F.FiniteFibres := (cleanRVMap_finite _).comp hf
    let g (a : A) (i : Fin k) : Section2.RV M :=
      ⟨(F a).val i, fun he => cleanRV_nonzero (f a).val i (congrArg Subtype.val he)⟩
    refine ⟨g, fun t => ?_, (rvMapGraph_definable_iff hc A g).mpr F.graph_definable⟩
    let b : DefSet.univ (rawRVSpace (M := M) k) S :=
      ⟨fun i => (t i).val, Set.mem_univ _⟩
    apply (hF b).subset
    intro a ha
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun ha i)

theorem rvDimension_eq_companion (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) m) S) (hne : A.carrier.Nonempty) :
    Section2.rvDimension S A.carrier = (rvDim A : WithBot ℕ) := by
  classical
  have hmin : Section2.RVHasFiniteMap S A.carrier (rvDim A) :=
    (rvFiniteMap_iff hc A (rvDim A)).mpr (rvDim_attained A)
  let d := sInf {k | Section2.RVHasFiniteMap S A.carrier k}
  have hd : Section2.RVHasFiniteMap S A.carrier d := by
    change sInf {k | Section2.RVHasFiniteMap S A.carrier k} ∈
      {k | Section2.RVHasFiniteMap S A.carrier k}
    exact Nat.sInf_mem ⟨rvDim A, hmin⟩
  have hle : d ≤ rvDim A := Nat.sInf_le hmin
  have hge : rvDim A ≤ d := by
    obtain ⟨f, hf⟩ := (rvFiniteMap_iff hc A d).mp hd
    exact (rvDim_le_iff A d).mpr ⟨d, le_rfl, f, hf⟩
  change (if A.carrier.Nonempty then (d : WithBot ℕ) else ⊥) = _
  rw [if_pos hne, hle.antisymm hge]

end DiamondIntegral.Section3
