import FubiniTheorems.Fubini.NativeRESChartClasses
import «section 4».BlowupChart

/-! Classes of definable pieces of an RES chart.

For an RES chart `C` and a definable subset `I` of its domain, `classOn C I` is the class of the
restriction of `C` to `I` (`0` if `I` is not a definable subset of the domain). It is additive on
disjoint pieces (`classOn_union`, `classOn_biUnion`), equal to the class of `C` on the whole
domain (`classOn_domain`), and equal to the class of any RES chart with the same arity and domain
(`classOn_eq_of_domain`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.RESPieces

open Classical
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 RVMeasuredCharts DiamondIntegral.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)}

/-- The class of the restriction of `C` to `I`. -/
def classOn {k : ℕ} (C : RESChart B k) (I : Set (Fin C.arity → M)) : RESDimensionFreeReduction.Ring B :=
  if h : DefinableOverBase B (fun _ : Fin C.arity => .rv) I ∧ I ⊆ C.domain then
    nativeRESChartClass (Section3RESChartCuts.restrict C I h.1 h.2)
  else 0

theorem classOn_eq {k : ℕ} (C : RESChart B k) (I : Set (Fin C.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin C.arity => .rv) I) (hs : I ⊆ C.domain) :
    classOn C I = nativeRESChartClass (Section3RESChartCuts.restrict C I hI hs) :=
  dite_cond_eq_true (eq_true ⟨hI, hs⟩)

/-- Two RES charts of the same arity with the same domain have the same class. -/
theorem class_eq_of_domain {k l : ℕ} (C : RESChart B k) (D : RESChart B l)
    (h : C.arity = D.arity) (hd : ∀ u : Fin C.arity → M, u ∈ C.domain ↔ (u ∘ Fin.cast h.symm) ∈ D.domain) :
    nativeRESChartClass C = nativeRESChartClass D := by
  obtain ⟨Cc, hfin⟩ := C
  obtain ⟨Dc, hfin'⟩ := D
  simp only at h hd
  refine nativeRESChartClass_iso _ _ (RVUnderlyingIsomorphisms.ofMap _ _ (fun u => u ∘ Fin.cast h.symm)
    ?_ ⟨fun u hu => (hd u).mp hu, fun u _ v _ huv => ?_, fun v hv => ⟨v ∘ Fin.cast h, (hd _).mpr ?_, ?_⟩⟩)
  · have hg := RVCoordinateMaps.coordinate_graph_definable B Cc.domain Cc.domain_definable (Fin.cast h.symm)
    exact hg
  · funext i
    have := congrFun huv (Fin.cast h i)
    simpa using this
  · convert hv using 1
    funext i; simp
  · funext i; simp

theorem classOn_domain {k : ℕ} (C : RESChart B k) : classOn C C.domain = nativeRESChartClass C := by
  rw [classOn_eq C C.domain C.domain_definable subset_rfl]
  exact class_eq_of_domain _ _ rfl fun u => by simp only [Fin.cast_refl, Function.comp_id]; rfl

theorem classOn_empty {k : ℕ} (C : RESChart B k) : classOn C ∅ = 0 := by
  unfold classOn
  split_ifs with h
  · exact nativeRESChartClass_empty _ rfl
  · rfl

/-- The class of a piece is the class of any RES chart of the same arity with that domain. -/
theorem classOn_eq_of_domain {k l : ℕ} (C : RESChart B k) (I : Set (Fin C.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin C.arity => .rv) I) (hs : I ⊆ C.domain)
    (D : RESChart B l) (h : C.arity = D.arity)
    (hd : ∀ u : Fin C.arity → M, u ∈ I ↔ (u ∘ Fin.cast h.symm) ∈ D.domain) :
    classOn C I = nativeRESChartClass D := by
  rw [classOn_eq C I hI hs]
  exact class_eq_of_domain _ D h hd

theorem classOn_union {k : ℕ} (C : RESChart B k) (I J : Set (Fin C.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin C.arity => .rv) I)
    (hJ : DefinableOverBase B (fun _ : Fin C.arity => .rv) J)
    (hsI : I ⊆ C.domain) (hsJ : J ⊆ C.domain) (hd : Disjoint I J) :
    classOn C (I ∪ J) = classOn C I + classOn C J := by
  have hIJ : DefinableOverBase B (fun _ : Fin C.arity => .rv) (I ∪ J) := hI.union hJ
  have hsIJ : I ∪ J ⊆ C.domain := Set.union_subset hsI hsJ
  rw [classOn_eq C _ hIJ hsIJ, classOn_eq C I hI hsI, classOn_eq C J hJ hsJ]
  let D := Section3RESChartCuts.restrict C (I ∪ J) hIJ hsIJ
  have hcut := nativeRESChartClass_cut D I hI Set.subset_union_left
  have e1 : nativeRESChartClass (Section3RESChartCuts.restrict D I hI Set.subset_union_left) =
      nativeRESChartClass (Section3RESChartCuts.restrict C I hI hsI) :=
    class_eq_of_domain _ _ rfl fun u => by simp only [Fin.cast_refl, Function.comp_id]; rfl
  have e2 : nativeRESChartClass (Section3RESChartCuts.outside D I hI) =
      nativeRESChartClass (Section3RESChartCuts.restrict C J hJ hsJ) := by
    refine class_eq_of_domain _ _ rfl fun u => ?_
    simp only [Fin.cast_refl, Function.comp_id]
    change u ∈ (I ∪ J) \ I ↔ u ∈ J
    exact ⟨fun ⟨h1, h2⟩ => h1.resolve_left h2, fun h => ⟨Or.inr h, Set.disjoint_right.mp hd h⟩⟩
  rw [← hcut, e1, e2]

theorem classOn_biUnion {k : ℕ} (C : RESChart B k) {ι : Type*} (T : Finset ι)
    (S : ι → Set (Fin C.arity → M)) (hS : ∀ i ∈ T, DefinableOverBase B (fun _ : Fin C.arity => .rv) (S i))
    (hs : ∀ i ∈ T, S i ⊆ C.domain) (hd : (T : Set ι).PairwiseDisjoint S) :
    classOn C (⋃ i ∈ T, S i) = ∑ i ∈ T, classOn C (S i) := by
  induction T using Finset.induction_on with
  | empty => simp [classOn_empty]
  | insert j T hj ih =>
    rw [Finset.sum_insert hj, Finset.set_biUnion_insert]
    have hT : DefinableOverBase B (fun _ : Fin C.arity => .rv) (⋃ i ∈ T, S i) := by
      have : ⋃ i ∈ T, S i = ⋃ i ∈ T.attach, S i.1 := by ext; simp
      rw [this]
      refine Finset.induction_on T.attach ?_ ?_
      · simpa using (BlowupChart.rv_universe_definable B C.arity).compl
      · intro i s _ h
        rw [Finset.set_biUnion_insert]
        exact (hS i.1 (Finset.mem_insert_of_mem i.2)).union h
    rw [classOn_union C _ _ (hS j (Finset.mem_insert_self j T)) hT
      (hs j (Finset.mem_insert_self j T))
      (Set.iUnion₂_subset fun i hi => hs i (Finset.mem_insert_of_mem hi))
      (by
        rw [Set.disjoint_iUnion₂_right]
        intro i hi
        exact hd (Finset.mem_insert_self j T) (Finset.mem_insert_of_mem hi)
          (fun h => hj (h ▸ hi))),
      ih (fun i hi => hS i (Finset.mem_insert_of_mem hi)) (fun i hi => hs i (Finset.mem_insert_of_mem hi))
        (hd.subset (by simp))]

end DiamondIntegral.Section8.RESPieces
