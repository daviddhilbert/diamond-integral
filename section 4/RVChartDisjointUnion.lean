import «section 4».RVChartRing
import «section 4».RVCoordinateMaps

/-! Actual disjoint unions of RV charts in a common finite tuple arity.
The helper data records that arity explicitly; conversion retains every
original-base coordinate and partial-volume graph. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVChartDisjointUnion
open RVMeasuredCharts FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure Data (B : Base (M := M)) (n k : ℕ) where
  domain : Set (Fin n → M)
  domain_definable : DefinableOverBase B (fun _ : Fin n => .rv) domain
  coordinate : (Fin n → M) → (Fin k → M)
  coordinate_definable : DefinableOverBase B (fun _ : Fin (k + n) => .rv) (graphOn domain coordinate)
  coordinate_proper : ∀ u ∈ domain, Proper (coordinate u)
  finite_fibres : ∀ t, {u | u ∈ domain ∧ coordinate u = t}.Finite
  volume : (Fin n → M) → Values.Gamma (M := M)
  volume_definable : DefinableOverBase B (fun _ : Fin (n + 1) => .rv)
    {w | Fin.tail w ∈ domain ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = volume (Fin.tail w)}

def Data.toChart {B : Base (M := M)} {n k : ℕ} (a : Data B n k) : Chart B k where
  arity := n
  domain := a.domain
  domain_definable := a.domain_definable
  coordinate := a.coordinate
  coordinate_definable := a.coordinate_definable
  coordinate_proper := a.coordinate_proper
  finite_fibres := a.finite_fibres
  volume := a.volume
  volume_definable := a.volume_definable

def ofChart {B : Base (M := M)} {k : ℕ} (a : Chart B k) : Data B a.arity k :=
  ⟨a.domain, a.domain_definable, a.coordinate, a.coordinate_definable, a.coordinate_proper,
    a.finite_fibres, a.volume, a.volume_definable⟩

theorem ofChart_toChart {B : Base (M := M)} {k : ℕ} (a : Chart B k) : (ofChart a).toChart = a := by
  cases a
  rfl

def piecewise {n : ℕ} {α : Type*} (I : Set (Fin n → M))
    (f g : (Fin n → M) → α) (u : Fin n → M) : α := if u ∈ I then f u else g u

theorem graphOn_piecewise {n k : ℕ} (I J : Set (Fin n → M)) (hd : Disjoint I J)
    (f g : (Fin n → M) → (Fin k → M)) :
    graphOn (I ∪ J) (piecewise I f g) = graphOn I f ∪ graphOn J g := by
  ext w
  change ((w ∘ headIndex k n ∈ I ∨ w ∘ headIndex k n ∈ J) ∧
    piecewise I f g (w ∘ headIndex k n) = w ∘ tailIndex k n) ↔
      (w ∘ headIndex k n ∈ I ∧ f (w ∘ headIndex k n) = w ∘ tailIndex k n) ∨
        (w ∘ headIndex k n ∈ J ∧ g (w ∘ headIndex k n) = w ∘ tailIndex k n)
  by_cases ha : w ∘ headIndex k n ∈ I
  · have hb : w ∘ headIndex k n ∉ J := fun hb => Set.disjoint_left.mp hd ha hb
    simp [piecewise, ha, hb]
  · simp [piecewise, ha]

def disjointUnion {B : Base (M := M)} {n k : ℕ} (a b : Data B n k) (hd : Disjoint a.domain b.domain) : Data B n k where
  domain := a.domain ∪ b.domain
  domain_definable := a.domain_definable.union b.domain_definable
  coordinate := piecewise a.domain a.coordinate b.coordinate
  coordinate_definable := by
    rw [graphOn_piecewise _ _ hd]
    exact a.coordinate_definable.union b.coordinate_definable
  coordinate_proper := by
    intro u hu
    by_cases ha : u ∈ a.domain
    · simpa only [piecewise, ite_eq_left ha] using a.coordinate_proper u ha
    · have hb : u ∈ b.domain := hu.resolve_left ha
      simpa only [piecewise, ite_eq_right ha] using b.coordinate_proper u hb
  finite_fibres := by
    intro t
    apply ((a.finite_fibres t).union (b.finite_fibres t)).subset
    rintro u ⟨hu, hf⟩
    by_cases ha : u ∈ a.domain
    · exact Or.inl ⟨ha, by simpa only [piecewise, ite_eq_left ha] using hf⟩
    · exact Or.inr ⟨hu.resolve_left ha, by simpa only [piecewise, ite_eq_right ha] using hf⟩
  volume := piecewise a.domain a.volume b.volume
  volume_definable := by
    have he : {w : Fin (n + 1) → M | Fin.tail w ∈ a.domain ∪ b.domain ∧ NonzeroRV (w 0) ∧
        codeValue (w 0) = piecewise a.domain a.volume b.volume (Fin.tail w)} =
        {w : Fin (n + 1) → M | Fin.tail w ∈ a.domain ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = a.volume (Fin.tail w)} ∪
          {w : Fin (n + 1) → M | Fin.tail w ∈ b.domain ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = b.volume (Fin.tail w)} := by
      ext w
      by_cases ha : Fin.tail w ∈ a.domain
      · have hb : Fin.tail w ∉ b.domain := fun hb => Set.disjoint_left.mp hd ha hb
        simp [piecewise, ha, hb]
      · simp [piecewise, ha]
    rw [he]
    exact a.volume_definable.union b.volume_definable

theorem disjointUnion_weight_left {B : Base (M := M)} {n k : ℕ} (a b : Data B n k)
    (hd : Disjoint a.domain b.domain) (u : Fin n → M) (hu : u ∈ a.domain) :
    (disjointUnion a b hd).toChart.correctedWeight u = a.toChart.correctedWeight u := by
  change piecewise a.domain a.volume b.volume u * (∏ i, codeValue (piecewise a.domain a.coordinate b.coordinate u i)) = _
  simp only [piecewise, ite_eq_left hu]
  rfl

theorem disjointUnion_weight_right {B : Base (M := M)} {n k : ℕ} (a b : Data B n k)
    (hd : Disjoint a.domain b.domain) (u : Fin n → M) (hu : u ∈ b.domain) :
    (disjointUnion a b hd).toChart.correctedWeight u = b.toChart.correctedWeight u := by
  have ha : u ∉ a.domain := fun ha => Set.disjoint_left.mp hd ha hu
  change piecewise a.domain a.volume b.volume u * (∏ i, codeValue (piecewise a.domain a.coordinate b.coordinate u i)) = _
  simp only [piecewise, ite_eq_right ha]
  rfl

def empty (B : Base (M := M)) (n k : ℕ) : Data B n k where
  domain := ∅
  domain_definable := DefinableOverBase.empty B _
  coordinate := fun _ _ => iRVZero
  coordinate_definable := by
    convert DefinableOverBase.empty B (fun _ : Fin (k + n) => .rv) using 1
    ext w
    change (w ∘ headIndex k n ∈ (∅ : Set (Fin n → M)) ∧ _ = _) ↔ False
    exact ⟨fun h => h.1.elim, fun h => h.elim⟩
  coordinate_proper := fun _ h => h.elim
  finite_fibres := fun _ => Set.finite_empty.subset (fun _ h => h.1)
  volume := fun _ => 1
  volume_definable := by
    convert DefinableOverBase.empty B (fun _ : Fin (n + 1) => .rv) using 1
    ext w
    change (Fin.tail w ∈ (∅ : Set (Fin n → M)) ∧ _ ∧ _) ↔ False
    exact ⟨fun h => h.1.elim, fun h => h.elim⟩

theorem packed_empty (B : Base (M := M)) (n k : ℕ) : RVMeasuredGroup.packed (empty B n k).toChart = ∅ := by
  ext z
  constructor
  · rintro ⟨u, _⟩
    exact u.property
  · intro h
    exact h.elim

theorem packed_disjointUnion {B : Base (M := M)} {n k : ℕ} (a b : Data B n k)
    (hd : Disjoint a.domain b.domain) :
    RVMeasuredGroup.packed (disjointUnion a b hd).toChart =
      RVMeasuredGroup.packed a.toChart ∪ RVMeasuredGroup.packed b.toChart := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    rcases u.property with ha | hb
    · refine Or.inl ⟨⟨u.val, ha⟩, ?_⟩
      exact congrArg (fun v : Values.Gamma (M := M) =>
        (⟨n, u.val, v⟩ : Σ m : ℕ, (Fin m → M) × Values.Gamma (M := M)))
          (disjointUnion_weight_left a b hd u.val ha).symm
    · refine Or.inr ⟨⟨u.val, hb⟩, ?_⟩
      exact congrArg (fun v : Values.Gamma (M := M) =>
        (⟨n, u.val, v⟩ : Σ m : ℕ, (Fin m → M) × Values.Gamma (M := M)))
          (disjointUnion_weight_right a b hd u.val hb).symm
  · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · refine ⟨⟨u.val, Or.inl u.property⟩, ?_⟩
      exact congrArg (fun v : Values.Gamma (M := M) =>
        (⟨n, u.val, v⟩ : Σ m : ℕ, (Fin m → M) × Values.Gamma (M := M)))
          (disjointUnion_weight_left a b hd u.val u.property)
    · refine ⟨⟨u.val, Or.inr u.property⟩, ?_⟩
      exact congrArg (fun v : Values.Gamma (M := M) =>
        (⟨n, u.val, v⟩ : Σ m : ℕ, (Fin m → M) × Values.Gamma (M := M)))
          (disjointUnion_weight_right a b hd u.val u.property)

theorem packed_inter_empty {B : Base (M := M)} {n k : ℕ} (a b : Data B n k)
    (hd : Disjoint a.domain b.domain) : RVMeasuredGroup.packed a.toChart ∩ RVMeasuredGroup.packed b.toChart = ∅ := by
  ext z
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    have he : (⟨n, u.val, a.toChart.correctedWeight u.val⟩ : Σ m : ℕ, (Fin m → M) × Values.Gamma (M := M)) =
        ⟨n, v.val, b.toChart.correctedWeight v.val⟩ := hu.trans hv.symm
    have hh : (u.val, a.toChart.correctedWeight u.val) = (v.val, b.toChart.correctedWeight v.val) :=
      eq_of_heq (Sigma.mk.inj_iff.mp he).2
    have huv : (u.val : Fin n → M) = v.val := congrArg Prod.fst hh
    exact Set.disjoint_left.mp hd u.property (Set.mem_of_eq_of_mem huv v.property)
  · intro h
    exact h.elim

theorem scissor {B : Base (M := M)} {n k : ℕ} (a b : Data B n k) (hd : Disjoint a.domain b.domain) :
    RVMeasuredGroup.Scissor a.toChart b.toChart (disjointUnion a b hd).toChart (empty B n k).toChart :=
  ⟨rfl, rfl, rfl, packed_disjointUnion a b hd, (packed_empty B n k).trans (packed_inter_empty a b hd).symm⟩

theorem class_disjointUnion {B : Base (M := M)} {n k : ℕ} (a b : Data B n k) (hd : Disjoint a.domain b.domain) :
    RVChartRing.objectClass (disjointUnion a b hd).toChart = RVChartRing.objectClass a.toChart + RVChartRing.objectClass b.toChart := by
  have hs := RVChartRing.objectClass_scissor _ _ _ _ (scissor a b hd)
  rw [RVChartRing.objectClass_empty (empty B n k).toChart rfl, add_zero] at hs
  exact hs

end DiamondIntegral.Section4.RVChartDisjointUnion
