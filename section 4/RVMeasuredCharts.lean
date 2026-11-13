import «section 4».GammaRVChartPresentation
import «section 4».GammaRVLifts

/-! Actual RV objects with partial Gamma volume forms over the original
real/Gamma parameter base. The coordinate map has proper RV outputs and
finite fibres. RES objects have finite full value patterns, including
infinity. Isomorphisms retain actual definable graphs and the corrected
weight equation. This module does not yet construct their Grothendieck
rings or a tensor decomposition. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVMeasuredCharts
open GammaRVChartPresentation FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def graphOn {m n : ℕ} (I : Set (Fin m → M)) (F : (Fin m → M) → (Fin n → M)) :
    Set (Fin (n + m) → M) :=
  {w | w ∘ headIndex n m ∈ I ∧ F (w ∘ headIndex n m) = w ∘ tailIndex n m}

structure Chart (B : Base (M := M)) (k : ℕ) where
  arity : ℕ
  domain : Set (Fin arity → M)
  domain_definable : DefinableOverBase B (fun _ : Fin arity => .rv) domain
  coordinate : (Fin arity → M) → (Fin k → M)
  coordinate_definable : DefinableOverBase B (fun _ : Fin (k + arity) => .rv) (graphOn domain coordinate)
  coordinate_proper : ∀ u ∈ domain, Proper (coordinate u)
  finite_fibres : ∀ t, {u | u ∈ domain ∧ coordinate u = t}.Finite
  volume : (Fin arity → M) → Values.Gamma (M := M)
  volume_definable : DefinableOverBase B (fun _ : Fin (arity + 1) => .rv)
    {w | Fin.tail w ∈ domain ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = volume (Fin.tail w)}

def Chart.correctedWeight {B : Base (M := M)} {k : ℕ} (a : Chart B k) (u : Fin a.arity → M) :
    Values.Gamma (M := M) := a.volume u * ∏ i, codeValue (a.coordinate u i)

def Chart.valuePattern {B : Base (M := M)} {k : ℕ} (a : Chart B k) (u : a.domain) :
    Fin a.arity → Values.GammaTop (M := M) :=
  fun i => Values.vrv ⟨u.val i, a.domain_definable.proper u.val u.property i⟩

structure RESChart (B : Base (M := M)) (k : ℕ) extends Chart B k where
  finite_values : (Set.range toChart.valuePattern).Finite

theorem Chart.zero_domain_finite {B : Base (M := M)} (a : Chart B 0) : a.domain.Finite := by
  apply (a.finite_fibres Fin.elim0).subset
  intro u hu
  exact ⟨hu, Subsingleton.elim _ _⟩

theorem Chart.finite_domain_values {B : Base (M := M)} {k : ℕ} (a : Chart B k)
    (ha : a.domain.Finite) : (Set.range a.valuePattern).Finite := by
  let : Finite a.domain := ha
  exact Set.finite_range _

def zeroRESChart {B : Base (M := M)} (a : Chart B 0) : RESChart B 0 :=
  ⟨a, a.finite_domain_values a.zero_domain_finite⟩

structure Iso {B : Base (M := M)} {k : ℕ} (a b : Chart B k) where
  equiv : a.domain ≃ b.domain
  graph_definable : DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv)
    {w | ∃ u : a.domain, w = join b.arity a.arity u.val (equiv u).val}
  weight_eq : ∀ u : a.domain, a.correctedWeight u.val = b.correctedWeight (equiv u).val

theorem correctedWeight_eq_iff {B : Base (M := M)} {k : ℕ} (a b : Chart B k)
    (u : Fin a.arity → M) (v : Fin b.arity → M) :
    a.correctedWeight u = b.correctedWeight v ↔
      a.volume u = b.volume v * (∏ i, codeValue (b.coordinate v i)) / (∏ i, codeValue (a.coordinate u i)) := by
  change a.volume u * _ = b.volume v * _ ↔ _
  exact (eq_div_iff_mul_eq').symm

theorem Iso.volume_eq {B : Base (M := M)} {k : ℕ} {a b : Chart B k}
    (F : Iso a b) (u : a.domain) :
    a.volume u.val = b.volume (F.equiv u).val *
      (∏ i, codeValue (b.coordinate (F.equiv u).val i)) / (∏ i, codeValue (a.coordinate u.val i)) :=
  (correctedWeight_eq_iff a b u.val (F.equiv u).val).mp (F.weight_eq u)

theorem constant_volume_definable (B : Base (M := M)) {n : ℕ} (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I)
    (γ : Values.Gamma (M := M)) (hγ : GammaDefinableClosureAtBase B γ) :
    DefinableOverBase B (fun _ : Fin (n + 1) => .rv)
      {w | Fin.tail w ∈ I ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = γ} := by
  have hd := hI.preimage_real (fun _ : Fin (n + 1) => .rv) Fin.succ
  have hv := hγ.preimage_real (fun _ : Fin (n + 1) => .rv) (fun _ : Fin 1 => (0 : Fin (n + 1)))
  have h := hd.inter hv
  convert h using 1
  ext w
  change (Fin.tail w ∈ I ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = γ) ↔
    ((w ∘ Fin.succ ∈ I ∧ w ∈ sortedUniverse (fun _ => .rv)) ∧
      (w 0 ∈ Values.gammaPullback {γ} ∧ w ∈ sortedUniverse (fun _ => .rv)))
  have htail : w ∘ Fin.succ = Fin.tail w := by funext i; rfl
  rw [htail]
  constructor
  · rintro ⟨hw, h0, he⟩
    have hs : w ∈ sortedUniverse (fun _ => .rv) := by
      intro i
      exact Fin.cases h0.1 (fun j => hI.proper _ hw j) i
    exact ⟨⟨hw, hs⟩, (gammaPullback_mem_codeValue_iff {γ} (w 0) h0).mpr he, hs⟩
  · rintro ⟨⟨hw, _⟩, hv, _⟩
    have h0 : NonzeroRV (w 0) := ⟨hv.1, hv.2.1⟩
    exact ⟨hw, h0, (gammaPullback_mem_codeValue_iff {γ} (w 0) h0).mp hv⟩

theorem zero_tuple_definable (B : Base (M := M)) :
    DefinableOverBase B (fun _ : Fin 0 => .rv) (Set.univ : Set (Fin 0 → M)) := by
  have h := real_definableOverBase B (fun _ : Fin 0 => .rv) _
    (sortedUniverse_definable B.real (fun _ : Fin 0 => .rv))
  convert h using 1
  ext z
  exact ⟨fun _ i => i.elim0, fun _ => Set.mem_univ z⟩

def weightedUnit (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : Chart B 0 where
  arity := 0
  domain := Set.univ
  domain_definable := zero_tuple_definable B
  coordinate := fun _ => Fin.elim0
  coordinate_definable := by
    convert zero_tuple_definable B using 1
    ext w
    exact ⟨fun _ => Set.mem_univ w, fun _ => ⟨Set.mem_univ _, Subsingleton.elim _ _⟩⟩
  coordinate_proper := fun _ _ i => i.elim0
  finite_fibres := fun _ => Set.toFinite _
  volume := fun _ => γ
  volume_definable := by
    have hd : DefinableOverBase B (fun _ : Fin 1 => .rv) {w | w 0 ∈ Values.gammaPullback {γ}} := hγ
    convert hd using 1
    ext w
    change (Fin.tail w ∈ Set.univ ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = γ) ↔
      w 0 ∈ Values.gammaPullback {γ}
    constructor
    · rintro ⟨_, ht, he⟩
      exact (gammaPullback_mem_codeValue_iff {γ} (w 0) ht).mpr he
    · intro hw
      have ht : NonzeroRV (w 0) := ⟨hw.1, hw.2.1⟩
      exact ⟨Set.mem_univ _, ht, (gammaPullback_mem_codeValue_iff {γ} (w 0) ht).mp hw⟩

theorem weightedUnit_correctedWeight (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) (u : Fin 0 → M) :
    (weightedUnit B γ hγ).correctedWeight u = γ := by
  simp [Chart.correctedWeight, weightedUnit]

def weightedRESUnit (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : RESChart B 0 where
  toChart := weightedUnit B γ hγ
  finite_values := by
    apply (Set.finite_singleton (Fin.elim0 : Fin 0 → Values.GammaTop (M := M))).subset
    rintro p ⟨u, rfl⟩
    exact Subsingleton.elim _ _

theorem weightedUnit_iso_forces_eq (B : Base (M := M)) (γ δ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) (hδ : GammaDefinableClosureAtBase B δ)
    (F : Iso (weightedUnit B γ hγ) (weightedUnit B δ hδ)) : γ = δ := by
  let u : (weightedUnit B γ hγ).domain := ⟨Fin.elim0, Set.mem_univ _⟩
  exact (weightedUnit_correctedWeight B γ hγ u.val).symm.trans
    ((F.weight_eq u).trans (weightedUnit_correctedWeight B δ hδ (F.equiv u).val))

end DiamondIntegral.Section4.RVMeasuredCharts
