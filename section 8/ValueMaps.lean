import «section 4».BlowupRelation
import «section 4».VariableApertureMeasuredComparison

/-! Definable `Γ`-valued maps on definable RV sets.

The library's `RVVolumeMaps.VolumeDefinable B I μ` says that the graph of `μ : (Fin n → M) → Γ` on
`I`, coded by nonzero RV elements, is definable over `B`. This file adds:

* `preimage_definable`: `{u ∈ I | μ u ∈ P}` is definable for a definable `P ⊆ Γ`;
* `image_definable`: `μ '' I` is definable;
* `volume_const`, `volume_union`, `volume_congr`, `volume_restrict`, `volume_prod`;
* `coord_volume_definable`: `u ↦ codeValue (u i)` (the value of a coordinate; `1` on the RV
  zero) is definable;
* `chart_coordinate_volume`, `weight_volume_definable`: the corrected weight of a chart is a
  definable map on its domain. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.ValueMaps

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 RVMeasuredCharts RVVolumeMaps FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] (B : Base (M := M))

local notation "Γ" => Values.Gamma (M := M)

theorem mem_volumeGraph {n : ℕ} {I : Set (Fin n → M)} {μ : (Fin n → M) → Γ}
    {w : Fin (n + 1) → M} :
    w ∈ volumeGraph I μ ↔ Fin.tail w ∈ I ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = μ (Fin.tail w) :=
  Iff.rfl

/-- Preimages of definable subsets of `Γ` under definable maps are definable. -/
theorem preimage_definable {n : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) {μ : (Fin n → M) → Γ}
    (hμ : VolumeDefinable B I μ) {P : Set Γ} (hP : GammaDefinableOverBase B P) :
    DefinableOverBase B (fun _ : Fin n => .rv) {u | u ∈ I ∧ μ u ∈ P} := by
  have hP' : DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ Values.gammaPullback P} := hP
  have h : DefinableOverBase B (fun _ : Fin n => .rv) ((fun w => w ∘ Fin.succ) ''
      (volumeGraph I μ ∩ {w | w ∘ (fun _ : Fin 1 => (0 : Fin (n + 1))) ∈
        {z | z 0 ∈ Values.gammaPullback P} ∧ w ∈ sortedUniverse (fun _ => .rv)})) :=
    (DefinableOverBase.inter hμ (hP'.preimage_real (fun _ : Fin (n + 1) => .rv)
      (fun _ : Fin 1 => (0 : Fin (n + 1))))).image_real Fin.succ
  convert h using 1
  refine Set.ext fun u => ⟨?_, ?_⟩
  · rintro ⟨hu, hPu⟩
    obtain ⟨a, ha, hav⟩ := EndpointLogic.codeValue_surjective (μ u)
    refine ⟨Fin.cons a u, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact ⟨by simpa [Fin.tail] using hu, ha, by simpa [Fin.tail] using hav⟩
    · show a ∈ Values.gammaPullback P
      rw [SpecialTransformations.Section4.GammaSyntax.mem_gammaPullback_iff]
      exact ⟨ha, hav ▸ hPu⟩
    · intro i
      exact Fin.cases ha.1 (fun j => hI.proper u hu j) i
    · funext j; rfl
  · rintro ⟨w, ⟨⟨hw1, hw2, hw3⟩, hw4, -⟩, rfl⟩
    have h4 : w 0 ∈ Values.gammaPullback P := hw4
    rw [SpecialTransformations.Section4.GammaSyntax.mem_gammaPullback_iff] at h4
    exact ⟨hw1, hw3 ▸ h4.2⟩

/-- Images of definable sets under definable maps are definable subsets of `Γ`. -/
theorem image_definable {n : ℕ} {I : Set (Fin n → M)} {μ : (Fin n → M) → Γ}
    (hμ : VolumeDefinable B I μ) : GammaDefinableOverBase B (μ '' I) := by
  have h : DefinableOverBase B (fun _ : Fin 1 => .rv)
      ((fun w => w ∘ (fun _ : Fin 1 => (0 : Fin (n + 1)))) '' volumeGraph I μ) :=
    DefinableOverBase.image_real hμ (fun _ : Fin 1 => (0 : Fin (n + 1)))
  show DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ Values.gammaPullback (μ '' I)}
  convert h using 1
  refine Set.ext fun z => ⟨?_, ?_⟩
  · intro hz
    have hz' : z 0 ∈ Values.gammaPullback (μ '' I) := hz
    rw [SpecialTransformations.Section4.GammaSyntax.mem_gammaPullback_iff] at hz'
    obtain ⟨h0, u, hu, huv⟩ := hz'
    refine ⟨Fin.cons (z 0) u, ⟨by simpa [Fin.tail] using hu, h0, by simpa [Fin.tail] using huv.symm⟩, ?_⟩
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩
    show w 0 ∈ Values.gammaPullback (μ '' I)
    rw [SpecialTransformations.Section4.GammaSyntax.mem_gammaPullback_iff]
    exact ⟨hw2, Fin.tail w, hw1, hw3.symm⟩

theorem volume_congr {n : ℕ} {I : Set (Fin n → M)} {μ ν : (Fin n → M) → Γ}
    (h : ∀ u ∈ I, μ u = ν u) (hμ : VolumeDefinable B I μ) : VolumeDefinable B I ν := by
  have he : volumeGraph I μ = volumeGraph I ν := Set.ext fun w =>
    ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3.trans (h _ h1)⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3.trans (h _ h1).symm⟩⟩
  unfold VolumeDefinable
  rw [← he]
  exact hμ

theorem volume_union {n : ℕ} {I J : Set (Fin n → M)} {μ : (Fin n → M) → Γ}
    (hI : VolumeDefinable B I μ) (hJ : VolumeDefinable B J μ) : VolumeDefinable B (I ∪ J) μ := by
  have he : volumeGraph (I ∪ J) μ = volumeGraph I μ ∪ volumeGraph J μ := Set.ext fun w =>
    ⟨fun ⟨h1, h2, h3⟩ => h1.elim (fun h => Or.inl ⟨h, h2, h3⟩) (fun h => Or.inr ⟨h, h2, h3⟩),
      fun h => h.elim (fun ⟨h1, h2, h3⟩ => ⟨Or.inl h1, h2, h3⟩)
        (fun ⟨h1, h2, h3⟩ => ⟨Or.inr h1, h2, h3⟩)⟩
  unfold VolumeDefinable
  rw [he]
  exact DefinableOverBase.union hI hJ

theorem volume_restrict {n : ℕ} {I J : Set (Fin n → M)} {μ : (Fin n → M) → Γ}
    (hμ : VolumeDefinable B I μ) (hJ : DefinableOverBase B (fun _ : Fin n => .rv) J) (hJI : J ⊆ I) :
    VolumeDefinable B J μ := by
  have h := DefinableOverBase.inter hμ (hJ.preimage_real (fun _ : Fin (n + 1) => .rv) Fin.succ)
  have he : volumeGraph J μ = volumeGraph I μ ∩
      {w | w ∘ Fin.succ ∈ J ∧ w ∈ sortedUniverse (fun _ : Fin (n + 1) => .rv)} := Set.ext fun w =>
    ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨hJI h1, h2, h3⟩, h1, fun i =>
      Fin.cases h2.1 (fun j => hJ.proper _ h1 j) i⟩,
      fun ⟨⟨_, h2, h3⟩, h4, _⟩ => ⟨h4, h2, h3⟩⟩
  unfold VolumeDefinable
  rw [he]
  exact h

theorem volume_const {n : ℕ} {I : Set (Fin n → M)} (hI : DefinableOverBase B (fun _ : Fin n => .rv) I)
    {c : Γ} (hc : GammaDefinableClosureAtBase B c) : VolumeDefinable B I (fun _ => c) := by
  have hc' : DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ Values.gammaPullback {c}} := hc
  have h := DefinableOverBase.inter (hI.preimage_real (fun _ : Fin (n + 1) => .rv) Fin.succ)
    (hc'.preimage_real (fun _ : Fin (n + 1) => .rv) (fun _ : Fin 1 => (0 : Fin (n + 1))))
  have he : volumeGraph I (fun _ => c) =
      {w | w ∘ Fin.succ ∈ I ∧ w ∈ sortedUniverse (fun _ : Fin (n + 1) => .rv)} ∩
      {w | w ∘ (fun _ : Fin 1 => (0 : Fin (n + 1))) ∈ {z | z 0 ∈ Values.gammaPullback {c}} ∧
        w ∈ sortedUniverse (fun _ : Fin (n + 1) => .rv)} := by
    refine Set.ext fun w => ⟨?_, ?_⟩
    · rintro ⟨h1, h2, h3⟩
      have hs : w ∈ sortedUniverse (fun _ : Fin (n + 1) => .rv) := fun i =>
        Fin.cases h2.1 (fun j => hI.proper _ h1 j) i
      refine ⟨⟨h1, hs⟩, ?_, hs⟩
      show w 0 ∈ Values.gammaPullback {c}
      rw [SpecialTransformations.Section4.GammaSyntax.mem_gammaPullback_iff]
      exact ⟨h2, h3⟩
    · rintro ⟨⟨h1, -⟩, h2, -⟩
      have h2' : w 0 ∈ Values.gammaPullback {c} := h2
      rw [SpecialTransformations.Section4.GammaSyntax.mem_gammaPullback_iff] at h2'
      exact ⟨h1, h2'.1, h2'.2⟩
  unfold VolumeDefinable
  rw [he]
  exact h

theorem volume_prod {n : ℕ} {I : Set (Fin n → M)} (hI : DefinableOverBase B (fun _ : Fin n => .rv) I)
    {ι : Type*} (s : Finset ι) (μ : ι → (Fin n → M) → Γ) (hμ : ∀ i ∈ s, VolumeDefinable B I (μ i)) :
    VolumeDefinable B I (fun u => ∏ i ∈ s, μ i u) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using volume_const B hI (GammaGroupNames.one_definable_base B)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact multiply_definable B I hI _ _ (hμ a (Finset.mem_insert_self a s))
      (ih fun i hi => hμ i (Finset.mem_insert_of_mem hi))

/-- The value of a coordinate (`1` on the RV zero) is a definable map. -/
theorem coord_volume_definable {n : ℕ} {I : Set (Fin n → M)}
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (i : Fin n) :
    VolumeDefinable B I (fun u => codeValue (u i)) := by
  have hnz : DefinableOverBase B (fun _ : Fin 1 => .rv) {z : Fin 1 → M | Proper z} :=
    GammaOrderLogic.proper_definable_base B 1
  let I₁ : Set (Fin n → M) := I ∩ {u | u ∘ (fun _ : Fin 1 => i) ∈ {z : Fin 1 → M | Proper z} ∧
    u ∈ sortedUniverse (fun _ : Fin n => .rv)}
  let I₀ : Set (Fin n → M) := I ∩ {u | u ∘ (fun _ : Fin 1 => i) ∈
    (sortedUniverse (fun _ : Fin 1 => .rv) \ {z : Fin 1 → M | Proper z}) ∧
    u ∈ sortedUniverse (fun _ : Fin n => .rv)}
  have hI₁ : DefinableOverBase B (fun _ : Fin n => .rv) I₁ :=
    DefinableOverBase.inter hI (hnz.preimage_real _ (fun _ : Fin 1 => i))
  have hI₀ : DefinableOverBase B (fun _ : Fin n => .rv) I₀ :=
    DefinableOverBase.inter hI (hnz.compl.preimage_real _ (fun _ : Fin 1 => i))
  have hcover : I = I₁ ∪ I₀ := by
    refine Set.ext fun u => ⟨fun hu => ?_, fun hu => hu.elim (fun h => h.1) (fun h => h.1)⟩
    have hs : u ∈ sortedUniverse (fun _ : Fin n => .rv) := fun j => hI.proper u hu j
    by_cases h : NonzeroRV (u i)
    · exact Or.inl ⟨hu, fun _ => h, hs⟩
    · exact Or.inr ⟨hu, ⟨fun _ => hI.proper u hu i, fun hp => h (hp 0)⟩, hs⟩
  have h₁ : VolumeDefinable B I₁ (fun u => codeValue (u i)) := by
    have hg := RVCoordinateMaps.coordinate_graph_definable B I₁ hI₁ (fun _ : Fin 1 => i)
    have hF : graphOn I₁ (fun u => u ∘ (fun _ : Fin 1 => i)) = graphOn I₁ (fun u => ![u i]) := by
      congr 1
      funext u l
      fin_cases l
      rfl
    rw [hF] at hg
    exact BlowupRelation.codeValue_volume_definable I₁ hI₁ (fun u => u i) hg
      (fun u hu => hu.2.1 0)
  have h₀ : VolumeDefinable B I₀ (fun u => codeValue (u i)) := by
    refine volume_congr B (fun u hu => ?_) (volume_const B hI₀ (GammaGroupNames.one_definable_base B))
    have hz : ¬ NonzeroRV (u i) := fun h => hu.2.1.2 fun _ => h
    simp only [codeValue, hz, ↓reduceDIte]
  rw [hcover]
  exact volume_union B h₁ h₀

/-- The value of a coordinate of the structural map of a chart is a definable map. -/
theorem chart_coordinate_volume {k : ℕ} (a : Chart B k) (j : Fin k) :
    VolumeDefinable B a.domain (fun x => codeValue (a.coordinate x j)) := by
  have h : DefinableOverBase B (fun _ : Fin (1 + a.arity) => .rv)
      (graphOn a.domain ((fun c => c ∘ (fun _ : Fin 1 => j)) ∘ a.coordinate)) :=
    RVGraphComposition.graph_compose_definable B a.domain
      (sortedUniverse (fun _ : Fin k => SortTag.rv)) a.coordinate
      (fun c => c ∘ (fun _ : Fin 1 => j)) a.coordinate_definable
      (RVCoordinateMaps.coordinate_graph_definable B _ (BlowupChart.rv_universe_definable B k)
        (fun _ : Fin 1 => j))
      (fun x hx l => (a.coordinate_proper x hx l).1)
  have he : ((fun c => c ∘ (fun _ : Fin 1 => j)) ∘ a.coordinate) =
      (fun x : Fin a.arity → M => ![a.coordinate x j]) := by
    funext x l
    fin_cases l
    rfl
  rw [he] at h
  exact BlowupRelation.codeValue_volume_definable a.domain a.domain_definable
    (fun x => a.coordinate x j) h (fun x hx => a.coordinate_proper x hx j)

/-- The corrected weight of a chart is a definable map on its domain. -/
theorem weight_volume_definable {k : ℕ} (a : Chart B k) :
    VolumeDefinable B a.domain a.correctedWeight :=
  multiply_definable B a.domain a.domain_definable a.volume _ a.volume_definable
    (volume_prod B a.domain_definable Finset.univ _ fun j _ => chart_coordinate_volume B a j)

end DiamondIntegral.Section8.ValueMaps
