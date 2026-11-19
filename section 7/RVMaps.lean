import «section 4».RVDefinableTupleMaps
import «section 4».RVVariableMultiplication
import «section 4».RVGraphComposition
import «section 4».RVCoordinateMaps
import «section 4».RVStrictBoundedComparison
import «section 4».VariableApertureAnnularDomains
import «section 4».RVSharpCharts
import «section 4».GammaChartOperations
import «section 7».BoundedClasses

/-! Original-base definability of partial RV maps built from coordinates,
maps with definable graphs and RV multiplication, and of strict comparisons of
valuations. These are the graph computations behind the comparison
isomorphisms of Lemma 7.5. No RV representative is named: every multiplier is a
coordinate or the value of a definable function on the actual domain. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.RVMaps
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)}

/-- A scalar map with a definable graph on `I`. -/
def ScalarDef (B : Base (M := M)) {n : ℕ} (I : Set (Fin n → M)) (g : (Fin n → M) → M) : Prop :=
  DefinableOverBase B (fun _ : Fin (1 + n) => .rv) (graphOn I (fun u => ![g u]))

/-- A tuple map with a definable graph on `I`. -/
def TupleDef (B : Base (M := M)) {n m : ℕ} (I : Set (Fin n → M)) (G : (Fin n → M) → (Fin m → M)) :
    Prop :=
  DefinableOverBase B (fun _ : Fin (m + n) => .rv) (graphOn I G)

theorem tupleDef_of_scalar {n m : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) {G : (Fin n → M) → (Fin m → M)}
    (h : ∀ i, ScalarDef B I (fun u => G u i)) : TupleDef B I G :=
  RVDefinableTupleMaps.graph_definable B I hI G h

theorem scalarDef_coord {n : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (p : Fin n) : ScalarDef B I (fun u => u p) := by
  have h := RVCoordinateMaps.coordinate_graph_definable B I hI ![p]
  have he : (fun u : Fin n → M => u ∘ ![p]) = (fun u => ![u p]) := by
    funext u i
    fin_cases i
    rfl
  unfold ScalarDef
  rw [← he]
  exact h

theorem tupleDef_coord {n m : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (π : Fin m → Fin n) :
    TupleDef B I (fun u => u ∘ π) :=
  RVCoordinateMaps.coordinate_graph_definable B I hI π

theorem tupleDef_comp {a b c : ℕ} {I : Set (Fin a → M)} {J : Set (Fin b → M)}
    {F : (Fin a → M) → (Fin b → M)} {G : (Fin b → M) → (Fin c → M)}
    (hF : TupleDef B I F) (hG : TupleDef B J G) (hmap : Set.MapsTo F I J) :
    TupleDef B I (G ∘ F) :=
  RVGraphComposition.graph_compose_definable B I J F G hF hG hmap

theorem scalarDef_comp {a b : ℕ} {I : Set (Fin a → M)} {J : Set (Fin b → M)}
    {F : (Fin a → M) → (Fin b → M)} {g : (Fin b → M) → M}
    (hF : TupleDef B I F) (hg : ScalarDef B J g) (hmap : Set.MapsTo F I J) :
    ScalarDef B I (fun u => g (F u)) :=
  tupleDef_comp (G := fun v => ![g v]) hF hg hmap

theorem scalarDef_mono {n : ℕ} {I J : Set (Fin n → M)} {g : (Fin n → M) → M}
    (hg : ScalarDef B J g) (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (hIJ : I ⊆ J) :
    ScalarDef B I g := by
  have h := BoundedClasses.graph_inter_definable J I (fun u => ![g u]) hg hI
  unfold ScalarDef
  rwa [Set.inter_eq_self_of_subset_right hIJ] at h

/-- The pair map `u ↦ (g u, h u)`. -/
def pair {n : ℕ} (g h : (Fin n → M) → M) : (Fin n → M) → (Fin 2 → M) := fun u => ![g u, h u]

theorem tupleDef_pair {n : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) {g h : (Fin n → M) → M}
    (hg : ScalarDef B I g) (hh : ScalarDef B I h) : TupleDef B I (pair g h) := by
  apply tupleDef_of_scalar hI
  intro i
  fin_cases i
  · exact hg
  · exact hh

theorem scalarDef_mul {n : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) {g h : (Fin n → M) → M}
    (hg : ScalarDef B I g) (hh : ScalarDef B I h) :
    ScalarDef B I (fun u => iRVMul (g u) (h u)) := by
  have hP := tupleDef_pair hI hg hh
  have hJ : DefinableOverBase B (fun _ : Fin 2 => .rv) (pair g h '' I) :=
    BoundedClasses.graph_image_definable I (pair g h) hP
  have hm := RVVariableMultiplication.scalar_graph_definable B (pair g h '' I) hJ 0 1
  exact scalarDef_comp (g := fun v : Fin 2 → M => iRVMul (v 0) (v 1)) hP hm
    (fun u hu => ⟨u, hu, rfl⟩)

/-! ### Strict comparison of valuations -/

/-- The chart of all nonzero RV elements in one coordinate. -/
def lineChart (B : Base (M := M)) : Chart B 1 :=
  RVSharpCharts.sharpChart (GammaChartOperations.ofTotal B 1 Set.univ
    (GammaFibreCounting.univ_definable_base B 1) (fun _ => 1)
    (GammaDefinableMaps.constant_definable B 1 (GammaGroupNames.one_definable_base B)))

theorem mem_lineChart {z : Fin 1 → M} (hz : NonzeroRV (z 0)) : z ∈ (lineChart B).domain := by
  refine ⟨fun i => ?_, Set.mem_univ _⟩
  fin_cases i
  exact ⟨hz.1, hz.2⟩

/-- The coordinate of the line chart. -/
abbrev lineIdx : Fin (lineChart B).arity := ⟨0, Nat.zero_lt_one⟩

theorem lineChart_nonzero : ∀ x ∈ (lineChart B).domain, NonzeroRV (x (lineIdx (B := B))) :=
  fun _ hx => ⟨(hx.1 0).1, (hx.1 0).2⟩

/-- The set of points of `I` where `vrv (g u) < vrv (h u)` is definable. -/
theorem lt_definable {n : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) {g h : (Fin n → M) → M}
    (hg : ScalarDef B I g) (hh : ScalarDef B I h)
    (hgn : ∀ u ∈ I, NonzeroRV (g u)) (hhn : ∀ u ∈ I, NonzeroRV (h u)) :
    DefinableOverBase B (fun _ : Fin n => .rv) {u | u ∈ I ∧ codeValue (g u) < codeValue (h u)} := by
  let F : (Fin n → M) → (Fin (1 + 1) → M) := fun u => join 1 1 ![g u] ![h u]
  have hF : TupleDef B I F := by
    apply tupleDef_of_scalar hI
    intro i
    have hi : i = headIndex 1 1 0 ∨ i = tailIndex 1 1 0 := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hi with rfl | rfl
    · simpa only [F, join_head, Matrix.cons_val_zero] using hg
    · simpa only [F, join_tail, Matrix.cons_val_zero] using hh
  have hD := VariableApertureRayCancellation.deepDomain_definable (lineChart B) lineIdx
  have hpre := RVStrictBoundedComparison.preimage_definable B I F hF _ hD
  convert hpre using 1
  apply Set.ext
  intro u
  constructor
  · rintro ⟨hu, hlt⟩
    refine ⟨hu, ?_⟩
    have hx : ![g u] ∈ (lineChart B).domain := mem_lineChart (hgn u hu)
    have hz : Proper ![h u] := fun i => by fin_cases i; exact ⟨(hhn u hu).1, (hhn u hu).2⟩
    exact (VariableApertureRayCancellation.deepDomain_join_iff (lineChart B) lineIdx lineChart_nonzero
      ![g u] hx ![h u] hz).mpr hlt
  · rintro ⟨hu, hmem⟩
    have hx : ![g u] ∈ (lineChart B).domain := mem_lineChart (hgn u hu)
    have hz : Proper ![h u] := fun i => by fin_cases i; exact ⟨(hhn u hu).1, (hhn u hu).2⟩
    exact ⟨hu, (VariableApertureRayCancellation.deepDomain_join_iff (lineChart B) lineIdx lineChart_nonzero
      ![g u] hx ![h u] hz).mp hmem⟩

/-- The set of points of `I` where `vrv (g u) ≤ vrv (h u)` is definable. -/
theorem le_definable {n : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) {g h : (Fin n → M) → M}
    (hg : ScalarDef B I g) (hh : ScalarDef B I h)
    (hgn : ∀ u ∈ I, NonzeroRV (g u)) (hhn : ∀ u ∈ I, NonzeroRV (h u)) :
    DefinableOverBase B (fun _ : Fin n => .rv) {u | u ∈ I ∧ codeValue (g u) ≤ codeValue (h u)} := by
  have hdiff := RVChartRestrictions.difference_definable B I _ hI (lt_definable hI hh hg hhn hgn)
  convert hdiff using 1
  apply Set.ext
  intro u
  constructor
  · rintro ⟨hu, hle⟩
    exact ⟨hu, fun hlt => absurd hle (not_le.mpr hlt.2)⟩
  · rintro ⟨hu, hn⟩
    exact ⟨hu, le_of_not_gt (fun hlt => hn ⟨hu, hlt⟩)⟩

end DiamondIntegral.Section7.RVMaps
