import «section 4».RVBoundedGrading
import «section 4».RVChartRestrictions
import «section 4».RVMeasuredIsomorphisms
import «section 4».RVNamedTuples

/-! Paper Definition 4.9 (doubly bounded RV categories) asks that
`valim(U) ⊆ [-γ, γ]^n`, so an object of the paper's category has no
coordinate equal to `∞`. The concrete Lean presentation `RVBoundedRing`
uses `RVMeasuredBounds.DomainBounded`, which only bounds the nonzero RV
coordinates; coordinates equal to `iRVZero` (the paper's `∞`) are left
unconstrained.

This file shows that the two conventions give isomorphic rings. A
`StrictChart` is a bounded chart all of whose domain coordinates differ
from `iRVZero`; `StrictRing` is the exact scissors presentation on strict
charts (unit, products, isomorphisms, empty objects and weighted scissors).
Forgetting infinity-freeness gives `toBounded`. Conversely, every bounded
chart splits by its `∞`-pattern `p` (the set of coordinates equal to
`iRVZero`) into definable pieces; deleting the `p`-coordinates turns each
piece into an isomorphic infinity-free chart (`strip`). Summing the classes
of the strips is an invariant of the bounded presentation, giving
`fromBounded`, and the two ring maps are mutually inverse. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVStrictBoundedComparison
open RVMeasuredCharts RVMeasuredBounds RVChartDisjointUnion RVChartRestrictions
open RVCoordinateMaps RVRealProducts FiniteTupleBlocks FiniteTupleGraphProduct

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### Strict (infinity-free) charts and their scissors ring -/

def InfinityFree {B : Base (M := M)} {k : ℕ} (a : Chart B k) : Prop :=
  ∀ u ∈ a.domain, ∀ i, u i ≠ iRVZero

structure StrictChart (B : Base (M := M)) (k : ℕ) extends RVBoundedCharts.BoundedChart B k where
  infinity_free : InfinityFree toChart

abbrev Generator (B : Base (M := M)) := Σ k, StrictChart B k

def symbol {B : Base (M := M)} {k : ℕ} (a : StrictChart B k) : FreeCommRing (Generator B) :=
  FreeCommRing.of ⟨k, a⟩

def unit (B : Base (M := M)) : StrictChart B 0 :=
  ⟨RVBoundedRing.unit B, fun _ _ i => i.elim0⟩

theorem product_infinityFree {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (ha : InfinityFree a) (hb : InfinityFree b) : InfinityFree (RVMeasuredProduct.product a b) := by
  intro u hu
  exact GammaBoundedProducts.all_coordinates b.arity a.arity (fun t => t ≠ iRVZero) u
    (fun i => ha _ hu.1 i) (fun i => hb _ hu.2 i)

def product {B : Base (M := M)} {k l : ℕ} (a : StrictChart B k) (b : StrictChart B l) :
    StrictChart B (l + k) :=
  ⟨RVBoundedCharts.product a.toBoundedChart b.toBoundedChart,
    product_infinityFree a.toChart b.toChart a.infinity_free b.infinity_free⟩

inductive Relation (B : Base (M := M)) : FreeCommRing (Generator B) → Prop where
  | unit : Relation B (symbol (unit B) - 1)
  | product {k l : ℕ} (a : StrictChart B k) (b : StrictChart B l) :
      Relation B (symbol (product a b) - symbol a * symbol b)
  | iso {k : ℕ} (a b : StrictChart B k) (F : Iso a.toChart b.toChart) : Relation B (symbol a - symbol b)
  | empty {k : ℕ} (a : StrictChart B k) (h : a.domain = ∅) : Relation B (symbol a)
  | scissor {k : ℕ} (a b c d : StrictChart B k)
      (h : RVMeasuredGroup.Scissor a.toChart b.toChart c.toChart d.toChart) :
      Relation B (symbol c + symbol d - symbol a - symbol b)

def relationIdeal (B : Base (M := M)) : Ideal (FreeCommRing (Generator B)) := Ideal.span {r | Relation B r}

def StrictRing (B : Base (M := M)) := FreeCommRing (Generator B) ⧸ relationIdeal B
  deriving CommRing

def objectClass {B : Base (M := M)} {k : ℕ} (a : StrictChart B k) : StrictRing B :=
  Ideal.Quotient.mk (relationIdeal B) (symbol a)

theorem relation_zero (B : Base (M := M)) (r : FreeCommRing (Generator B)) (hr : Relation B r) :
    Ideal.Quotient.mk (relationIdeal B) r = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)

theorem objectClass_unit (B : Base (M := M)) : objectClass (unit B) = 1 := by
  have h := relation_zero B _ Relation.unit
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

theorem objectClass_product {B : Base (M := M)} {k l : ℕ} (a : StrictChart B k) (b : StrictChart B l) :
    objectClass (product a b) = objectClass a * objectClass b := by
  have h := relation_zero B _ (Relation.product a b)
  rw [map_sub, map_mul] at h
  exact sub_eq_zero.mp h

theorem objectClass_iso {B : Base (M := M)} {k : ℕ} {a b : StrictChart B k} (F : Iso a.toChart b.toChart) :
    objectClass a = objectClass b := by
  have h := relation_zero B _ (Relation.iso a b F)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem objectClass_empty {B : Base (M := M)} {k : ℕ} (a : StrictChart B k) (ha : a.domain = ∅) :
    objectClass a = 0 := relation_zero B _ (Relation.empty a ha)

theorem objectClass_scissor {B : Base (M := M)} {k : ℕ} (a b c d : StrictChart B k)
    (h : RVMeasuredGroup.Scissor a.toChart b.toChart c.toChart d.toChart) :
    objectClass c + objectClass d = objectClass a + objectClass b := by
  have hr := relation_zero B _ (Relation.scissor a b c d h)
  rw [map_sub, map_sub, map_add, sub_sub] at hr
  exact sub_eq_zero.mp hr

structure Invariant (B : Base (M := M)) (R : Type*) [CommRing R] where
  value : ∀ k, StrictChart B k → R
  unit : value 0 (unit B) = 1
  product : ∀ k l (a : StrictChart B k) (b : StrictChart B l),
    value (l + k) (product a b) = value k a * value l b
  iso : ∀ k (a b : StrictChart B k) (_F : Iso a.toChart b.toChart), value k a = value k b
  empty : ∀ k (a : StrictChart B k), a.domain = ∅ → value k a = 0
  scissor : ∀ k (a b c d : StrictChart B k), RVMeasuredGroup.Scissor a.toChart b.toChart c.toChart d.toChart →
    value k c + value k d = value k a + value k b

def freeMap (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) :
    FreeCommRing (Generator B) →+* R := FreeCommRing.lift (fun a => f.value a.1 a.2)

theorem freeMap_symbol (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    {k : ℕ} (a : StrictChart B k) : freeMap B f (symbol a) = f.value k a := FreeCommRing.lift_of _ _

theorem invariant_relation_zero (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    (r : FreeCommRing (Generator B)) (hr : Relation B r) : freeMap B f r = 0 := by
  cases hr with
  | unit => rw [map_sub, map_one, freeMap_symbol, f.unit, sub_self]
  | product a b => rw [map_sub, map_mul, freeMap_symbol, freeMap_symbol, freeMap_symbol, f.product, sub_self]
  | iso a b F => rw [map_sub, freeMap_symbol, freeMap_symbol, f.iso _ a b F, sub_self]
  | empty a h => rw [freeMap_symbol, f.empty _ a h]
  | scissor a b c d h =>
    simp only [map_sub, map_add, freeMap_symbol, sub_sub]
    exact sub_eq_zero.mpr (f.scissor _ a b c d h)

theorem invariant_ideal_zero (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) :
    relationIdeal B ≤ RingHom.ker (freeMap B f) := by
  apply Ideal.span_le.mpr
  intro r hr
  exact invariant_relation_zero B f r hr

def lift (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) : StrictRing B →+* R :=
  Ideal.Quotient.lift (relationIdeal B) (freeMap B f) (fun _ hr => invariant_ideal_zero B f hr)

theorem lift_objectClass (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    {k : ℕ} (a : StrictChart B k) : lift B f (objectClass a) = f.value k a := freeMap_symbol B f a

theorem hom_ext (B : Base (M := M)) {R : Type*} [CommRing R]
    (f g : StrictRing B →+* R) (h : ∀ k (a : StrictChart B k), f (objectClass a) = g (objectClass a)) :
    f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro a
  exact h a.1 a.2

theorem lift_unique (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    (g : StrictRing B →+* R) (h : ∀ k (a : StrictChart B k), g (objectClass a) = f.value k a) :
    g = lift B f := by
  apply hom_ext B
  intro k a
  exact (h k a).trans (lift_objectClass B f a).symm

/-! ### Forgetting infinity-freeness -/

def toBoundedInvariant (B : Base (M := M)) : Invariant B (RVBoundedRing.Ring B) where
  value _ a := RVBoundedRing.objectClass a.toBoundedChart
  unit := RVBoundedRing.objectClass_unit B
  product _ _ a b := RVBoundedRing.objectClass_product a.toBoundedChart b.toBoundedChart
  iso _ _ _ F := RVBoundedRing.objectClass_iso F
  empty _ a h := RVBoundedRing.objectClass_empty a.toBoundedChart h
  scissor _ a b c d h := RVBoundedRing.objectClass_scissor a.toBoundedChart b.toBoundedChart
    c.toBoundedChart d.toBoundedChart h

def toBounded (B : Base (M := M)) : StrictRing B →+* RVBoundedRing.Ring B := lift B (toBoundedInvariant B)

theorem toBounded_objectClass (B : Base (M := M)) {k : ℕ} (a : StrictChart B k) :
    toBounded B (objectClass a) = RVBoundedRing.objectClass a.toBoundedChart :=
  lift_objectClass B (toBoundedInvariant B) a

/-! ### Definability of preimages, images and restrictions of graphs -/

theorem graph_restrict_definable (B : Base (M := M)) {n m : ℕ} (X Y : Set (Fin n → M))
    (f : (Fin n → M) → (Fin m → M)) (hYX : Y ⊆ X)
    (hY : DefinableOverBase B (fun _ : Fin n => .rv) Y)
    (hf : DefinableOverBase B (fun _ : Fin (m + n) => .rv) (graphOn X f)) :
    DefinableOverBase B (fun _ : Fin (m + n) => .rv) (graphOn Y f) := by
  have h := hf.inter (hY.preimage_real (fun _ : Fin (m + n) => .rv) (headIndex m n))
  convert h using 1
  ext w
  change (w ∘ headIndex m n ∈ Y ∧ f (w ∘ headIndex m n) = w ∘ tailIndex m n) ↔
    (w ∘ headIndex m n ∈ X ∧ f (w ∘ headIndex m n) = w ∘ tailIndex m n) ∧
      w ∘ headIndex m n ∈ Y ∧ w ∈ sortedUniverse (fun _ => .rv)
  constructor
  · rintro ⟨hy, he⟩
    have hg : w ∈ graphOn X f := ⟨hYX hy, he⟩
    exact ⟨hg, hy, hf.proper w hg⟩
  · exact fun h => ⟨h.2.1, h.1.2⟩

theorem preimage_definable (B : Base (M := M)) {n m : ℕ} (X : Set (Fin n → M))
    (f : (Fin n → M) → (Fin m → M))
    (hf : DefinableOverBase B (fun _ : Fin (m + n) => .rv) (graphOn X f))
    (T : Set (Fin m → M)) (hT : DefinableOverBase B (fun _ : Fin m => .rv) T) :
    DefinableOverBase B (fun _ : Fin n => .rv) {u | u ∈ X ∧ f u ∈ T} := by
  have h : DefinableOverBase B (fun _ : Fin n => .rv)
      ((fun w => w ∘ headIndex m n) '' (graphOn X f ∩
        {w | w ∘ tailIndex m n ∈ T ∧ w ∈ sortedUniverse (fun _ : Fin (m + n) => .rv)})) :=
    (hf.inter (hT.preimage_real (fun _ : Fin (m + n) => .rv) (tailIndex m n))).image_real (headIndex m n)
  convert h using 1
  ext u
  constructor
  · rintro ⟨hu, hfu⟩
    have hg : join m n u (f u) ∈ graphOn X f := (graphOn_exists X f _).mpr ⟨u, hu, rfl⟩
    refine ⟨join m n u (f u), ⟨hg, ?_, hf.proper _ hg⟩, funext (join_head m n u (f u))⟩
    rw [show join m n u (f u) ∘ tailIndex m n = f u from funext (join_tail m n u (f u))]
    exact hfu
  · rintro ⟨w, ⟨hw, ht, _⟩, rfl⟩
    refine ⟨hw.1, ?_⟩
    rw [hw.2]
    exact ht

theorem image_definable (B : Base (M := M)) {n m : ℕ} (X : Set (Fin n → M))
    (f : (Fin n → M) → (Fin m → M))
    (hf : DefinableOverBase B (fun _ : Fin (m + n) => .rv) (graphOn X f))
    (S : Set (Fin n → M)) (hS : DefinableOverBase B (fun _ : Fin n => .rv) S) :
    DefinableOverBase B (fun _ : Fin m => .rv) (f '' (X ∩ S)) := by
  have h : DefinableOverBase B (fun _ : Fin m => .rv)
      ((fun w => w ∘ tailIndex m n) '' (graphOn X f ∩
        {w | w ∘ headIndex m n ∈ S ∧ w ∈ sortedUniverse (fun _ : Fin (m + n) => .rv)})) :=
    (hf.inter (hS.preimage_real (fun _ : Fin (m + n) => .rv) (headIndex m n))).image_real (tailIndex m n)
  convert h using 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hg : join m n u (f u) ∈ graphOn X f := (graphOn_exists X f _).mpr ⟨u, hu.1, rfl⟩
    refine ⟨join m n u (f u), ⟨hg, ?_, hf.proper _ hg⟩, funext (join_tail m n u (f u))⟩
    rw [show join m n u (f u) ∘ headIndex m n = u from funext (join_head m n u (f u))]
    exact hu.2
  · rintro ⟨w, ⟨hw, hs, _⟩, rfl⟩
    exact ⟨w ∘ headIndex m n, ⟨hw.1, hs⟩, hw.2⟩

/-- A measured isomorphism given by a map with a definable graph. -/
def mapIso {B : Base (M := M)} {k : ℕ} (x y : Chart B k) (f : (Fin x.arity → M) → (Fin y.arity → M))
    (hf : DefinableOverBase B (fun _ : Fin (y.arity + x.arity) => .rv) (graphOn x.domain f))
    (hbij : Set.BijOn f x.domain y.domain)
    (hw : ∀ u ∈ x.domain, x.correctedWeight u = y.correctedWeight (f u)) : Iso x y where
  equiv := Set.BijOn.equiv f hbij
  graph_definable := by
    have he : {w | ∃ u : x.domain, w = join y.arity x.arity u.val (Set.BijOn.equiv f hbij u).val} =
        graphOn x.domain f := by
      ext w
      rw [graphOn_exists]
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨u.val, u.property, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨⟨u, hu⟩, rfl⟩
    change DefinableOverBase B (fun _ : Fin (y.arity + x.arity) => .rv)
      {w | ∃ u : x.domain, w = join y.arity x.arity u.val (Set.BijOn.equiv f hbij u).val}
    rw [he]
    exact hf
  weight_eq := fun u => hw u.val u.property

/-! ### Infinity patterns -/

/-- The tuples whose `∞`-coordinates (those equal to `iRVZero`) are exactly `p`. -/
def patternSet {n : ℕ} (p : Finset (Fin n)) : Set (Fin n → M) :=
  {u | u ∈ sortedUniverse (fun _ : Fin n => .rv) ∧ ∀ i, (u i = iRVZero ↔ i ∈ p)}

def zeroLocus {n : ℕ} (u : Fin n → M) : Finset (Fin n) := Finset.univ.filter (fun i => u i = iRVZero)

omit [M ⊨ Axioms.ACVF] in
theorem mem_patternSet_zeroLocus {n : ℕ} (u : Fin n → M)
    (hu : u ∈ sortedUniverse (fun _ : Fin n => .rv)) : u ∈ patternSet (zeroLocus u) :=
  ⟨hu, fun i => by simp [zeroLocus]⟩

omit [M ⊨ Axioms.ACVF] in
theorem pattern_unique {n : ℕ} {p q : Finset (Fin n)} {u : Fin n → M}
    (hp : u ∈ patternSet p) (hq : u ∈ patternSet q) : p = q := by
  ext i
  exact (hp.2 i).symm.trans (hq.2 i)

theorem patternSet_definable (B : Base (M := M)) {n : ℕ} (p : Finset (Fin n)) :
    DefinableOverBase B (fun _ : Fin n => .rv) (patternSet p) := by
  let Z : Fin n → Set (Fin n → M) := fun i =>
    {z | z ∘ (fun _ : Fin 1 => i) ∈ {z : Fin 1 → M | z 0 ∈ ({iRVZero} : Set M)} ∧
      z ∈ sortedUniverse (fun _ : Fin n => .rv)}
  have hZ : ∀ i, DefinableOverBase B (fun _ : Fin n => .rv) (Z i) := fun i =>
    (RVNamedTuples.zero_definable B).preimage_real (fun _ : Fin n => .rv) (fun _ : Fin 1 => i)
  let F : Fin n → Set (Fin n → M) := fun i =>
    if i ∈ p then Z i else sortedUniverse (fun _ : Fin n => .rv) \ Z i
  have hF : ∀ i ∈ (Finset.univ : Finset (Fin n)), DefinableOverBase B (fun _ : Fin n => .rv) (F i) := by
    intro i _
    by_cases hi : i ∈ p
    · have he : F i = Z i := ite_eq_left hi
      rw [he]
      exact hZ i
    · have he : F i = sortedUniverse (fun _ : Fin n => .rv) \ Z i := ite_eq_right hi
      rw [he]
      exact (hZ i).compl
  have h := DefinableOverBase.finite_iInter Finset.univ F hF
  convert h using 1
  ext u
  constructor
  · rintro ⟨hs, hp⟩
    refine ⟨hs, fun i _ => ?_⟩
    by_cases hi : i ∈ p
    · have he : F i = Z i := ite_eq_left hi
      rw [he]
      exact ⟨(hp i).mpr hi, hs⟩
    · have he : F i = sortedUniverse (fun _ : Fin n => .rv) \ Z i := ite_eq_right hi
      rw [he]
      exact ⟨hs, fun hz => hi ((hp i).mp hz.1)⟩
  · rintro ⟨hs, hF'⟩
    refine ⟨hs, fun i => ?_⟩
    have hi' := hF' i (Finset.mem_univ i)
    by_cases hi : i ∈ p
    · have he : F i = Z i := ite_eq_left hi
      rw [he] at hi'
      exact ⟨fun _ => hi, fun _ => hi'.1⟩
    · have he : F i = sortedUniverse (fun _ : Fin n => .rv) \ Z i := ite_eq_right hi
      rw [he] at hi'
      exact ⟨fun hz => (hi'.2 ⟨hz, hs⟩).elim, fun h => (hi h).elim⟩

/-! ### Deleting the `∞`-coordinates of a pattern -/

def stripArity {n : ℕ} (p : Finset (Fin n)) : ℕ := pᶜ.card

def stripIndex {n : ℕ} (p : Finset (Fin n)) (j : Fin (stripArity p)) : Fin n := (pᶜ.equivFin.symm j).val

theorem stripIndex_not_mem {n : ℕ} (p : Finset (Fin n)) (j : Fin (stripArity p)) : stripIndex p j ∉ p :=
  Finset.mem_compl.mp (pᶜ.equivFin.symm j).property

/-- Reinsert `iRVZero` at the coordinates of `p`. -/
def unstrip {n : ℕ} (p : Finset (Fin n)) (v : Fin (stripArity p) → M) : Fin n → M :=
  fun i => if h : i ∈ pᶜ then v (pᶜ.equivFin ⟨i, h⟩) else iRVZero

omit [M ⊨ Axioms.ACVF] in
theorem unstrip_comp {n : ℕ} {p : Finset (Fin n)} {u : Fin n → M} (hu : u ∈ patternSet p) :
    unstrip p (u ∘ stripIndex p) = u := by
  funext i
  by_cases h : i ∈ pᶜ
  · rw [unstrip, dite_eq_left h]
    change u ((pᶜ.equivFin.symm (pᶜ.equivFin ⟨i, h⟩)).val) = u i
    rw [Equiv.symm_apply_apply]
  · rw [unstrip, dite_eq_right h]
    exact ((hu.2 i).mpr (by simpa using h)).symm

omit [M ⊨ Axioms.ACVF] in
theorem strip_injOn {n : ℕ} (p : Finset (Fin n)) :
    Set.InjOn (fun u : Fin n → M => u ∘ stripIndex p) (patternSet p) := by
  intro u hu v hv h
  rw [← unstrip_comp hu, ← unstrip_comp hv]
  exact congrArg (unstrip p) h

def stripDomain {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (p : Finset (Fin n)) :
    Set (Fin (stripArity p) → M) :=
  (fun u => u ∘ stripIndex p) '' (D.domain ∩ patternSet p)

theorem stripDomain_cases {B : Base (M := M)} {n k : ℕ} {D : Data B n k} {p : Finset (Fin n)}
    {v : Fin (stripArity p) → M} (hv : v ∈ stripDomain D p) :
    ∃ u, u ∈ D.domain ∧ u ∈ patternSet p ∧ u ∘ stripIndex p = v ∧ unstrip p v = u := by
  obtain ⟨u, hu, rfl⟩ := hv
  exact ⟨u, hu.1, hu.2, rfl, unstrip_comp hu.2⟩

def coordIndex {n : ℕ} (k : ℕ) (p : Finset (Fin n)) : Fin (k + stripArity p) → Fin (k + n) :=
  join k (stripArity p) (fun i => headIndex k n (stripIndex p i)) (tailIndex k n)

omit [LRV.Structure M] [M ⊨ Axioms.ACVF] in
theorem join_coordIndex {n k : ℕ} (p : Finset (Fin n)) (u : Fin n → M) (c : Fin k → M) :
    join k n u c ∘ coordIndex k p = join k (stripArity p) (u ∘ stripIndex p) c := by
  apply block_ext k (stripArity p)
  · funext i
    simp [coordIndex, Function.comp_apply]
  · funext i
    simp [coordIndex, Function.comp_apply]

def volIndex {n : ℕ} (p : Finset (Fin n)) : Fin (stripArity p + 1) → Fin (n + 1) :=
  Fin.cons 0 (fun j => (stripIndex p j).succ)

omit [LRV.Structure M] [M ⊨ Axioms.ACVF] in
theorem comp_volIndex {n : ℕ} (p : Finset (Fin n)) (z : Fin (n + 1) → M) :
    z ∘ volIndex p = Fin.cons (z 0) (Fin.tail z ∘ stripIndex p) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [volIndex]
  · simp [volIndex, Fin.tail]

theorem stripDomain_definable {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (p : Finset (Fin n)) :
    DefinableOverBase B (fun _ : Fin (stripArity p) => .rv) (stripDomain D p) :=
  (D.domain_definable.inter (patternSet_definable B p)).image_real (stripIndex p)

theorem strip_coordinate_definable {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (p : Finset (Fin n)) :
    DefinableOverBase B (fun _ : Fin (k + stripArity p) => .rv)
      (graphOn (stripDomain D p) (fun v => D.coordinate (unstrip p v))) := by
  have h : DefinableOverBase B (fun _ : Fin (k + stripArity p) => .rv)
      ((fun w => w ∘ coordIndex k p) '' (graphOn D.domain D.coordinate ∩
        {w | w ∘ headIndex k n ∈ patternSet p ∧ w ∈ sortedUniverse (fun _ : Fin (k + n) => .rv)})) :=
    (D.coordinate_definable.inter ((patternSet_definable B p).preimage_real
      (fun _ : Fin (k + n) => .rv) (headIndex k n))).image_real (coordIndex k p)
  convert h using 1
  ext w
  rw [graphOn_exists]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨u, hu, hup, rfl, hun⟩ := stripDomain_cases hv
    have hg : join k n u (D.coordinate u) ∈ graphOn D.domain D.coordinate :=
      (graphOn_exists _ _ _).mpr ⟨u, hu, rfl⟩
    refine ⟨join k n u (D.coordinate u), ⟨hg, ?_, D.coordinate_definable.proper _ hg⟩, ?_⟩
    · rw [show join k n u (D.coordinate u) ∘ headIndex k n = u from funext (join_head k n u _)]
      exact hup
    · dsimp only
      rw [join_coordIndex, hun]
  · rintro ⟨z, ⟨hz, hzp, _⟩, rfl⟩
    obtain ⟨u, hu, rfl⟩ := (graphOn_exists _ _ _).mp hz
    have hh : join k n u (D.coordinate u) ∘ headIndex k n = u := funext (join_head k n u _)
    change join k n u (D.coordinate u) ∘ headIndex k n ∈ patternSet p at hzp
    rw [hh] at hzp
    refine ⟨u ∘ stripIndex p, ⟨u, ⟨hu, hzp⟩, rfl⟩, ?_⟩
    dsimp only
    rw [join_coordIndex, unstrip_comp hzp]

theorem strip_volume_definable {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (p : Finset (Fin n)) :
    DefinableOverBase B (fun _ : Fin (stripArity p + 1) => .rv)
      {w | Fin.tail w ∈ stripDomain D p ∧ NonzeroRV (w 0) ∧
        codeValue (w 0) = D.volume (unstrip p (Fin.tail w))} := by
  have h : DefinableOverBase B (fun _ : Fin (stripArity p + 1) => .rv)
      ((fun z => z ∘ volIndex p) ''
        ({w : Fin (n + 1) → M | Fin.tail w ∈ D.domain ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = D.volume (Fin.tail w)} ∩
          {z | z ∘ Fin.succ ∈ patternSet p ∧ z ∈ sortedUniverse (fun _ : Fin (n + 1) => .rv)})) :=
    (D.volume_definable.inter ((patternSet_definable B p).preimage_real
      (fun _ : Fin (n + 1) => .rv) Fin.succ)).image_real (volIndex p)
  convert h using 1
  ext w
  constructor
  · rintro ⟨hv, h0, hvol⟩
    obtain ⟨u, hu, hup, hut, hun⟩ := stripDomain_cases hv
    have hz : Fin.cons (w 0) u ∈ {w : Fin (n + 1) → M | Fin.tail w ∈ D.domain ∧ NonzeroRV (w 0) ∧
        codeValue (w 0) = D.volume (Fin.tail w)} := by
      refine ⟨?_, ?_, ?_⟩
      · rw [Fin.tail_cons]
        exact hu
      · rw [Fin.cons_zero]
        exact h0
      · rw [Fin.cons_zero, Fin.tail_cons, hvol, hun]
    refine ⟨Fin.cons (w 0) u, ⟨hz, ?_, D.volume_definable.proper _ hz⟩, ?_⟩
    · change Fin.tail (Fin.cons (w 0) u : Fin (n + 1) → M) ∈ patternSet p
      rw [Fin.tail_cons]
      exact hup
    · dsimp only
      rw [comp_volIndex, Fin.cons_zero, Fin.tail_cons, hut, Fin.cons_self_tail]
  · rintro ⟨z, ⟨⟨hz1, hz0, hzv⟩, hzp, _⟩, rfl⟩
    change Fin.tail z ∈ patternSet p at hzp
    dsimp only
    rw [comp_volIndex]
    change Fin.tail (Fin.cons (z 0) (Fin.tail z ∘ stripIndex p) : Fin (stripArity p + 1) → M) ∈ stripDomain D p ∧
      NonzeroRV ((Fin.cons (z 0) (Fin.tail z ∘ stripIndex p) : Fin (stripArity p + 1) → M) 0) ∧
      codeValue ((Fin.cons (z 0) (Fin.tail z ∘ stripIndex p) : Fin (stripArity p + 1) → M) 0) =
        D.volume (unstrip p (Fin.tail (Fin.cons (z 0) (Fin.tail z ∘ stripIndex p) : Fin (stripArity p + 1) → M)))
    rw [Fin.tail_cons, Fin.cons_zero]
    refine ⟨⟨Fin.tail z, ⟨hz1, hzp⟩, rfl⟩, hz0, ?_⟩
    rw [unstrip_comp hzp]
    exact hzv

/-- The chart obtained from the `p`-piece of `D` by deleting its `∞`-coordinates. -/
def strip {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (p : Finset (Fin n)) : Data B (stripArity p) k where
  domain := stripDomain D p
  domain_definable := stripDomain_definable D p
  coordinate := fun v => D.coordinate (unstrip p v)
  coordinate_definable := strip_coordinate_definable D p
  coordinate_proper := by
    intro v hv
    obtain ⟨u, hu, _, _, hun⟩ := stripDomain_cases hv
    rw [hun]
    exact D.coordinate_proper u hu
  finite_fibres := by
    intro t
    apply ((D.finite_fibres t).image (fun u => u ∘ stripIndex p)).subset
    rintro v ⟨hv, hvt⟩
    obtain ⟨u, hu, _, hut, hun⟩ := stripDomain_cases hv
    rw [hun] at hvt
    exact ⟨u, ⟨hu, hvt⟩, hut⟩
  volume := fun v => D.volume (unstrip p v)
  volume_definable := strip_volume_definable D p

/-- The `p`-piece of `D`: the tuples of `D` with `∞`-pattern exactly `p`. -/
def piece {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (p : Finset (Fin n)) : Data B n k :=
  inside D (patternSet p) (patternSet_definable B p)

theorem strip_weight {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (p : Finset (Fin n))
    (u : Fin n → M) (hu : u ∈ patternSet p) :
    (strip D p).toChart.correctedWeight (u ∘ stripIndex p) = D.toChart.correctedWeight u := by
  exact congrArg D.toChart.correctedWeight (unstrip_comp hu)

/-- Every piece is isomorphic to its strip by deleting the `∞`-coordinates. -/
def stripIso {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (p : Finset (Fin n)) :
    Iso (piece D p).toChart (strip D p).toChart :=
  coordinateIso _ _ (stripIndex p)
    ⟨fun u hu => ⟨u, hu, rfl⟩, (strip_injOn p).mono (fun _ hu => hu.2), fun _ hv => hv⟩
    (fun u hu => (strip_weight D p u hu.2).symm)

theorem strip_bounded {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (hD : DomainBounded D.toChart)
    (p : Finset (Fin n)) : DomainBounded (strip D p).toChart := by
  obtain ⟨β, hβ⟩ := hD
  refine ⟨β, fun v hv j hj => ?_⟩
  obtain ⟨u, hu, _, rfl, _⟩ := stripDomain_cases hv
  exact hβ u hu (stripIndex p j) hj

theorem strip_infinityFree {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (p : Finset (Fin n)) :
    InfinityFree (strip D p).toChart := by
  intro v hv j hj
  obtain ⟨u, _, hup, rfl, _⟩ := stripDomain_cases hv
  exact stripIndex_not_mem p j ((hup.2 (stripIndex p j)).mp hj)

/-! ### Classes of chart data in the two rings -/

def Admissible {B : Base (M := M)} {n k : ℕ} (D : Data B n k) : Prop :=
  DomainBounded D.toChart ∧ InfinityFree D.toChart

def toStrict {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (h : Admissible D) : StrictChart B k :=
  ⟨⟨D.toChart, h.1⟩, h.2⟩

/-- The strict class of chart data, set to zero off the admissible (strict) data. -/
def sclass {B : Base (M := M)} {n k : ℕ} (D : Data B n k) : StrictRing B :=
  if h : Admissible D then objectClass (toStrict D h) else 0

/-- The bounded class of chart data, set to zero off the bounded data. -/
def bclass {B : Base (M := M)} {n k : ℕ} (D : Data B n k) : RVBoundedRing.Ring B :=
  if h : DomainBounded D.toChart then RVBoundedRing.objectClass (⟨D.toChart, h⟩ : RVBoundedCharts.BoundedChart B k)
  else 0

theorem sclass_eq {B : Base (M := M)} {n k : ℕ} {D : Data B n k} (h : Admissible D) :
    sclass D = objectClass (toStrict D h) := dite_eq_left h

theorem bclass_eq {B : Base (M := M)} {n k : ℕ} {D : Data B n k} (h : DomainBounded D.toChart) :
    bclass D = RVBoundedRing.objectClass (⟨D.toChart, h⟩ : RVBoundedCharts.BoundedChart B k) := dite_eq_left h

theorem bounded_mono {B : Base (M := M)} {n k : ℕ} {D E : Data B n k} (hsub : D.domain ⊆ E.domain)
    (hE : DomainBounded E.toChart) : DomainBounded D.toChart := by
  obtain ⟨β, hβ⟩ := hE
  exact ⟨β, fun u hu i hi => hβ u (hsub hu) i hi⟩

theorem admissible_mono {B : Base (M := M)} {n k : ℕ} {D E : Data B n k} (hsub : D.domain ⊆ E.domain)
    (hE : Admissible E) : Admissible D :=
  ⟨bounded_mono hsub hE.1, fun u hu => hE.2 u (hsub hu)⟩

theorem admissible_strip {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (hD : DomainBounded D.toChart)
    (p : Finset (Fin n)) : Admissible (strip D p) :=
  ⟨strip_bounded D hD p, strip_infinityFree D p⟩

theorem sclass_empty {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (h : D.domain = ∅) : sclass D = 0 := by
  unfold sclass
  split_ifs with ha
  · exact objectClass_empty _ h
  · rfl

theorem bclass_empty {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (h : D.domain = ∅) : bclass D = 0 := by
  unfold bclass
  split_ifs with ha
  · exact RVBoundedRing.objectClass_empty _ h
  · rfl

theorem sclass_iso {B : Base (M := M)} {n m k : ℕ} {D : Data B n k} {E : Data B m k}
    (hD : Admissible D) (hE : Admissible E) (F : Iso D.toChart E.toChart) : sclass D = sclass E := by
  rw [sclass_eq hD, sclass_eq hE]
  exact objectClass_iso F

theorem bclass_iso {B : Base (M := M)} {n m k : ℕ} {D : Data B n k} {E : Data B m k}
    (hD : DomainBounded D.toChart) (hE : DomainBounded E.toChart) (F : Iso D.toChart E.toChart) :
    bclass D = bclass E := by
  rw [bclass_eq hD, bclass_eq hE]
  exact RVBoundedRing.objectClass_iso F

theorem sclass_ofChart {B : Base (M := M)} {k : ℕ} (a : StrictChart B k) :
    sclass (ofChart a.toChart) = objectClass a := by
  rw [sclass_eq (D := ofChart a.toChart) ⟨a.domain_bounded, a.infinity_free⟩]
  rfl

theorem bclass_ofChart {B : Base (M := M)} {k : ℕ} (a : RVBoundedCharts.BoundedChart B k) :
    bclass (ofChart a.toChart) = RVBoundedRing.objectClass a := by
  rw [bclass_eq (D := ofChart a.toChart) a.domain_bounded]
  rfl

theorem toBounded_sclass {B : Base (M := M)} {n k : ℕ} {D : Data B n k} (h : Admissible D) :
    toBounded B (sclass D) = bclass D := by
  rw [sclass_eq h, toBounded_objectClass, bclass_eq h.1]
  rfl

/-! ### Weighted point sets and scissors -/

def pairs {B : Base (M := M)} {n k : ℕ} (D : Data B n k) : Set ((Fin n → M) × Values.Gamma (M := M)) :=
  {z | z.1 ∈ D.domain ∧ z.2 = D.toChart.correctedWeight z.1}

theorem packed_eq {B : Base (M := M)} {n k : ℕ} (D : Data B n k) :
    RVMeasuredGroup.packed D.toChart = Sigma.mk n '' pairs D := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(u.val, D.toChart.correctedWeight u.val), ⟨u.property, rfl⟩, rfl⟩
  · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
    change w = D.toChart.correctedWeight x at hw
    subst hw
    exact ⟨⟨x, hx⟩, rfl⟩

theorem sigma_image_injective (n : ℕ) :
    Function.Injective (Set.image (Sigma.mk (β := fun m : ℕ => (Fin m → M) × Values.Gamma (M := M)) n)) :=
  Set.image_injective.mpr sigma_mk_injective

theorem scissor_of_pairs {B : Base (M := M)} {n k : ℕ} (a b c d : Data B n k)
    (hc : pairs c = pairs a ∪ pairs b) (hd : pairs d = pairs a ∩ pairs b) :
    RVMeasuredGroup.Scissor a.toChart b.toChart c.toChart d.toChart := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · rw [packed_eq, packed_eq, packed_eq, hc, Set.image_union]
  · rw [packed_eq, packed_eq, packed_eq, hd, Set.image_inter sigma_mk_injective]

theorem pairs_of_scissor {B : Base (M := M)} {n k : ℕ} (a b c d : Data B n k)
    (h : RVMeasuredGroup.Scissor a.toChart b.toChart c.toChart d.toChart) :
    pairs c = pairs a ∪ pairs b ∧ pairs d = pairs a ∩ pairs b := by
  obtain ⟨_, _, _, hc, hd⟩ := h
  rw [packed_eq, packed_eq, packed_eq, ← Set.image_union] at hc
  rw [packed_eq, packed_eq, packed_eq, ← Set.image_inter sigma_mk_injective] at hd
  exact ⟨sigma_image_injective n hc, sigma_image_injective n hd⟩

theorem weight_congr {B : Base (M := M)} {n k : ℕ} {a c : Data B n k}
    (hc : a.coordinate = c.coordinate) (hv : a.volume = c.volume) :
    a.toChart.correctedWeight = c.toChart.correctedWeight := by
  funext u
  change a.volume u * ∏ i, codeValue (a.coordinate u i) = c.volume u * ∏ i, codeValue (c.coordinate u i)
  rw [hc, hv]

/-- Two disjoint data with the coordinates and volume of `c` covering `c` form a scissor with
the empty data. -/
theorem split_scissor {B : Base (M := M)} {n k : ℕ} (a b c : Data B n k)
    (hca : a.coordinate = c.coordinate) (hva : a.volume = c.volume)
    (hcb : b.coordinate = c.coordinate) (hvb : b.volume = c.volume)
    (hdom : c.domain = a.domain ∪ b.domain) (hdisj : Disjoint a.domain b.domain) :
    RVMeasuredGroup.Scissor a.toChart b.toChart c.toChart (RVChartDisjointUnion.empty B n k).toChart := by
  have hwa := weight_congr hca hva
  have hwb := weight_congr hcb hvb
  apply scissor_of_pairs
  · ext ⟨x, w⟩
    change (x ∈ c.domain ∧ w = c.toChart.correctedWeight x) ↔
      (x ∈ a.domain ∧ w = a.toChart.correctedWeight x) ∨ (x ∈ b.domain ∧ w = b.toChart.correctedWeight x)
    rw [hwa, hwb, hdom, Set.mem_union, or_and_right]
  · ext ⟨x, w⟩
    constructor
    · rintro ⟨hx, _⟩
      exact hx.elim
    · rintro ⟨⟨ha, _⟩, ⟨hb, _⟩⟩
      exact (Set.disjoint_left.mp hdisj ha hb).elim

theorem sclass_add {B : Base (M := M)} {n k : ℕ} (a b c : Data B n k) (hc : Admissible c)
    (hca : a.coordinate = c.coordinate) (hva : a.volume = c.volume)
    (hcb : b.coordinate = c.coordinate) (hvb : b.volume = c.volume)
    (hdom : c.domain = a.domain ∪ b.domain) (hdisj : Disjoint a.domain b.domain) :
    sclass c = sclass a + sclass b := by
  have ha : Admissible a := admissible_mono (hdom ▸ Set.subset_union_left) hc
  have hb : Admissible b := admissible_mono (hdom ▸ Set.subset_union_right) hc
  have he : Admissible (RVChartDisjointUnion.empty B n k) :=
    ⟨⟨1, fun _ hu => hu.elim⟩, fun _ hu => hu.elim⟩
  have hs := objectClass_scissor (toStrict a ha) (toStrict b hb) (toStrict c hc) (toStrict _ he)
    (split_scissor a b c hca hva hcb hvb hdom hdisj)
  rw [objectClass_empty (toStrict _ he) rfl, add_zero] at hs
  rw [sclass_eq hc, sclass_eq ha, sclass_eq hb]
  exact hs

theorem bclass_add {B : Base (M := M)} {n k : ℕ} (a b c : Data B n k) (hc : DomainBounded c.toChart)
    (hca : a.coordinate = c.coordinate) (hva : a.volume = c.volume)
    (hcb : b.coordinate = c.coordinate) (hvb : b.volume = c.volume)
    (hdom : c.domain = a.domain ∪ b.domain) (hdisj : Disjoint a.domain b.domain) :
    bclass c = bclass a + bclass b := by
  have ha : DomainBounded a.toChart := bounded_mono (hdom ▸ Set.subset_union_left) hc
  have hb : DomainBounded b.toChart := bounded_mono (hdom ▸ Set.subset_union_right) hc
  have he : DomainBounded (RVChartDisjointUnion.empty B n k).toChart := ⟨1, fun _ hu => hu.elim⟩
  have hs := RVBoundedRing.objectClass_scissor ⟨a.toChart, ha⟩ ⟨b.toChart, hb⟩ ⟨c.toChart, hc⟩ ⟨_, he⟩
    (split_scissor a b c hca hva hcb hvb hdom hdisj)
  rw [RVBoundedRing.objectClass_empty ⟨_, he⟩ rfl, add_zero] at hs
  rw [bclass_eq hc, bclass_eq ha, bclass_eq hb]
  exact hs

/-- Finite additivity over a finite definable partition with common coordinates and volume
(for any additive monoid of values, so it also applies to positive classes). -/
theorem sum_cover {B : Base (M := M)} {A : Type*} [AddCommMonoid A] {n k : ℕ}
    (f : Data B n k → A) (Adm : Data B n k → Prop)
    (hAdm : ∀ a c : Data B n k, a.domain ⊆ c.domain → Adm c → Adm a)
    (hempty : ∀ a : Data B n k, a.domain = ∅ → f a = 0)
    (hadd : ∀ a b c : Data B n k, Adm c → a.coordinate = c.coordinate → a.volume = c.volume →
      b.coordinate = c.coordinate → b.volume = c.volume →
      c.domain = a.domain ∪ b.domain → Disjoint a.domain b.domain → f c = f a + f b)
    {ι : Type} (E : ι → Data B n k) (s : Finset ι) :
    ∀ c : Data B n k, Adm c → (∀ j ∈ s, (E j).coordinate = c.coordinate ∧ (E j).volume = c.volume) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (E i).domain (E j).domain) →
      c.domain = ⋃ j ∈ s, (E j).domain → f c = ∑ j ∈ s, f (E j) := by
  induction s using Finset.induction_on with
  | empty =>
    intro c _ _ _ hcov
    rw [Finset.sum_empty]
    apply hempty
    rw [hcov]
    simp
  | @insert j s hj ih =>
    intro c hc hE hdisj hcov
    have hsub : (⋃ i ∈ s, (E i).domain) ⊆ c.domain := by
      rw [hcov, Finset.set_biUnion_insert]
      exact Set.subset_union_right
    let c' := restrict c (⋃ i ∈ s, (E i).domain)
      (DefinableOverBase.finite_iUnion s (fun i => (E i).domain) (fun i _ => (E i).domain_definable)) hsub
    have hc' : Adm c' := hAdm c' c hsub hc
    have hj' := hE j (Finset.mem_insert_self j s)
    have h1 : f c = f (E j) + f c' := by
      apply hadd (E j) c' c hc hj'.1 hj'.2 rfl rfl
      · rw [hcov, Finset.set_biUnion_insert]
        rfl
      · change Disjoint (E j).domain (⋃ i ∈ s, (E i).domain)
        rw [Set.disjoint_iUnion₂_right]
        intro i hi
        exact hdisj j (Finset.mem_insert_self j s) i (Finset.mem_insert_of_mem hi)
          (fun h => hj (h ▸ hi))
    have h2 : f c' = ∑ i ∈ s, f (E i) :=
      ih c' hc' (fun i hi => hE i (Finset.mem_insert_of_mem hi))
        (fun i hi i' hi' hne => hdisj i (Finset.mem_insert_of_mem hi) i' (Finset.mem_insert_of_mem hi') hne) rfl
    rw [Finset.sum_insert hj, h1, h2]

/-- A bounded chart is the sum of its `∞`-pattern pieces in the bounded ring. -/
theorem bclass_pieces {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (hD : DomainBounded D.toChart) :
    bclass D = ∑ p : Finset (Fin n), bclass (piece D p) := by
  refine sum_cover bclass (fun x => DomainBounded x.toChart) (fun a c h hc => bounded_mono h hc)
    bclass_empty bclass_add (piece D) Finset.univ D hD (fun _ _ => ⟨rfl, rfl⟩) ?_ ?_
  · intro i _ j _ hne
    exact Set.disjoint_left.mpr (fun u hu hv => hne (pattern_unique hu.2 hv.2))
  · ext u
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
    constructor
    · intro hu
      exact ⟨zeroLocus u, hu, mem_patternSet_zeroLocus u (D.domain_definable.proper u hu)⟩
    · rintro ⟨p, hu, _⟩
      exact hu

/-- A strip splits along any finite definable partition of the underlying piece. -/
theorem sclass_strip_split {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (hD : DomainBounded D.toChart)
    {ι : Type} [Fintype ι] (X : ι → Set (Fin n → M))
    (hX : ∀ j, DefinableOverBase B (fun _ : Fin n => .rv) (X j)) (p : Finset (Fin n))
    (hcover : ∀ u ∈ D.domain ∩ patternSet p, ∃ j, u ∈ X j)
    (hdisj : ∀ u ∈ D.domain ∩ patternSet p, ∀ i j, u ∈ X i → u ∈ X j → i = j) :
    sclass (strip D p) = ∑ j, sclass (strip (inside D (X j) (hX j)) p) := by
  refine sum_cover sclass Admissible (fun a c h hc => admissible_mono h hc) sclass_empty sclass_add
    (fun j => strip (inside D (X j) (hX j)) p) Finset.univ (strip D p) (admissible_strip D hD p)
    (fun _ _ => ⟨rfl, rfl⟩) ?_ ?_
  · intro i _ j _ hne
    apply Set.disjoint_left.mpr
    rintro v ⟨u, hu, rfl⟩ ⟨u', hu', he⟩
    have huu : u' = u := strip_injOn p hu'.2 hu.2 he
    subst huu
    exact hne (hdisj u' ⟨hu.1.1, hu.2⟩ i j hu.1.2 hu'.1.2)
  · ext v
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨j, hj⟩ := hcover u hu
      exact ⟨j, u, ⟨⟨hu.1, hj⟩, hu.2⟩, rfl⟩
    · rintro ⟨j, u, hu, rfl⟩
      exact ⟨u, ⟨hu.1.1, hu.2⟩, rfl⟩

/-! ### The `∞`-pattern decomposition is an invariant of the bounded presentation -/

/-- The sum of the strict classes of the strips of all `∞`-pattern pieces of a chart. -/
def rho {B : Base (M := M)} {k : ℕ} (a : Chart B k) : StrictRing B :=
  ∑ p : Finset (Fin a.arity), sclass (strip (ofChart a) p)

theorem rho_empty {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain = ∅) : rho a = 0 :=
  Finset.sum_eq_zero (fun p _ => sclass_empty _ (by
    change (fun u => u ∘ stripIndex p) '' (a.domain ∩ patternSet p) = ∅
    rw [ha, Set.empty_inter, Set.image_empty]))

/-- On infinity-free data the empty-pattern piece is everything. -/
def pieceEmptyIso {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (hD : InfinityFree D.toChart) :
    Iso (piece D ∅).toChart D.toChart :=
  coordinateIso _ _ (fun i => i)
    ⟨fun _ hu => hu.1, fun _ _ _ _ h => h, fun v hv => ⟨v, ⟨hv, D.domain_definable.proper v hv,
      fun i => ⟨fun h => (hD v hv i h).elim, fun h => (Finset.notMem_empty i h).elim⟩⟩, rfl⟩⟩
    (fun _ _ => rfl)

/-- For a strict chart only the empty pattern contributes, and its strip is the chart itself. -/
theorem rho_strict {B : Base (M := M)} {k : ℕ} (a : StrictChart B k) : rho a.toChart = objectClass a := by
  have hA : Admissible (ofChart a.toChart) := ⟨a.domain_bounded, a.infinity_free⟩
  have hP : Admissible (piece (ofChart a.toChart) ∅) := admissible_mono (fun _ hu => hu.1) hA
  unfold rho
  rw [Finset.sum_eq_single_of_mem ∅ (Finset.mem_univ _) ?_]
  · rw [← sclass_iso hP (admissible_strip _ hA.1 ∅) (stripIso _ ∅),
      sclass_iso hP hA (pieceEmptyIso _ hA.2), sclass_ofChart]
  · intro p _ hp
    apply sclass_empty
    ext v
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨u, hu, rfl⟩
    obtain ⟨i, hi⟩ := Finset.nonempty_of_ne_empty hp
    exact a.infinity_free u hu.1 i ((hu.2.2 i).mpr hi)

/-! #### Scissors -/

def stripPair {n : ℕ} (p : Finset (Fin n)) (z : (Fin n → M) × Values.Gamma (M := M)) :
    (Fin (stripArity p) → M) × Values.Gamma (M := M) :=
  (z.1 ∘ stripIndex p, z.2)

theorem stripPair_injOn {n : ℕ} (p : Finset (Fin n)) :
    Set.InjOn (stripPair (M := M) p) {z | z.1 ∈ patternSet p} := by
  intro z hz z' hz' h
  have h1 : z.1 ∘ stripIndex p = z'.1 ∘ stripIndex p := congrArg Prod.fst h
  have h2 : (stripPair p z).2 = (stripPair p z').2 := congrArg Prod.snd h
  exact Prod.ext (strip_injOn p hz hz' h1) h2

theorem pairs_strip {B : Base (M := M)} {n k : ℕ} (D : Data B n k) (p : Finset (Fin n)) :
    pairs (strip D p) = stripPair p '' (pairs D ∩ {z | z.1 ∈ patternSet p}) := by
  ext ⟨v, w⟩
  constructor
  · rintro ⟨hv, hw⟩
    obtain ⟨u, hu, hup, rfl, _⟩ := stripDomain_cases hv
    refine ⟨(u, w), ⟨⟨hu, ?_⟩, hup⟩, rfl⟩
    exact hw.trans (strip_weight D p u hup)
  · rintro ⟨⟨u, w'⟩, ⟨⟨hu, hw⟩, hup⟩, he⟩
    simp only [stripPair, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨⟨u, ⟨hu, hup⟩, rfl⟩, hw.trans (strip_weight D p u hup).symm⟩

theorem strip_scissor {B : Base (M := M)} {n k : ℕ} (a b c d : Data B n k)
    (h : RVMeasuredGroup.Scissor a.toChart b.toChart c.toChart d.toChart) (p : Finset (Fin n)) :
    RVMeasuredGroup.Scissor (strip a p).toChart (strip b p).toChart (strip c p).toChart (strip d p).toChart := by
  obtain ⟨hc, hd⟩ := pairs_of_scissor a b c d h
  apply scissor_of_pairs
  · rw [pairs_strip, pairs_strip, pairs_strip, hc, Set.union_inter_distrib_right, Set.image_union]
  · rw [pairs_strip, pairs_strip, pairs_strip, hd, Set.inter_inter_distrib_right]
    exact (stripPair_injOn p).image_inter Set.inter_subset_right Set.inter_subset_right

def castArity {B : Base (M := M)} {n m k : ℕ} (h : n = m) (D : Data B n k) : Data B m k := h ▸ D

theorem castArity_packed {B : Base (M := M)} {n m k : ℕ} (h : n = m) (D : Data B n k) :
    RVMeasuredGroup.packed (castArity h D).toChart = RVMeasuredGroup.packed D.toChart := by
  subst h
  rfl

theorem castArity_bounded {B : Base (M := M)} {n m k : ℕ} (h : n = m) (D : Data B n k)
    (hD : DomainBounded D.toChart) : DomainBounded (castArity h D).toChart := by
  subst h
  exact hD

theorem castArity_sum {B : Base (M := M)} {n m k : ℕ} (h : n = m) (D : Data B n k) :
    ∑ p : Finset (Fin m), sclass (strip (castArity h D) p) = ∑ p : Finset (Fin n), sclass (strip D p) := by
  subst h
  rfl

theorem rho_scissor {B : Base (M := M)} {k : ℕ} (a b c d : Chart B k)
    (ha : DomainBounded a) (hb : DomainBounded b) (hc : DomainBounded c) (hd : DomainBounded d)
    (h : RVMeasuredGroup.Scissor a b c d) : rho c + rho d = rho a + rho b := by
  obtain ⟨hab, hac, had, hcu, hdi⟩ := h
  let b' := castArity hab.symm (ofChart b)
  let c' := castArity hac.symm (ofChart c)
  let d' := castArity had.symm (ofChart d)
  have hs : RVMeasuredGroup.Scissor (ofChart a).toChart b'.toChart c'.toChart d'.toChart := by
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · rw [castArity_packed, castArity_packed]
      exact hcu
    · rw [castArity_packed, castArity_packed]
      exact hdi
  have hb' := castArity_bounded hab.symm (ofChart b) hb
  have hc' := castArity_bounded hac.symm (ofChart c) hc
  have hd' := castArity_bounded had.symm (ofChart d) hd
  unfold rho
  rw [← castArity_sum hab.symm (ofChart b), ← castArity_sum hac.symm (ofChart c),
    ← castArity_sum had.symm (ofChart d), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [sclass_eq (admissible_strip (ofChart a) ha p), sclass_eq (admissible_strip _ hb' p),
    sclass_eq (admissible_strip _ hc' p), sclass_eq (admissible_strip _ hd' p)]
  exact objectClass_scissor _ _ _ _ (strip_scissor (ofChart a) b' c' d' hs p)

/-! #### Isomorphisms -/

theorem rho_iso {B : Base (M := M)} {k : ℕ} (a b : Chart B k) (ha : DomainBounded a) (hb : DomainBounded b)
    (F : Iso a b) : rho a = rho b := by
  let U := RVMeasuredIsomorphisms.underlying F
  let f := U.extension
  have hbij : Set.BijOn f a.domain b.domain := U.extension_bijOn
  have hgraph : DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv) (graphOn a.domain f) :=
    U.extension_graph
  have hw : ∀ u ∈ a.domain, a.correctedWeight u = b.correctedWeight (f u) := fun u hu =>
    (F.weight_eq ⟨u, hu⟩).trans (congrArg b.correctedWeight (U.extension_on ⟨u, hu⟩).symm)
  let Q : Finset (Fin b.arity) → Set (Fin a.arity → M) := fun q => {u | u ∈ a.domain ∧ f u ∈ patternSet q}
  have hQ : ∀ q, DefinableOverBase B (fun _ : Fin a.arity => .rv) (Q q) := fun q =>
    preimage_definable B a.domain f hgraph (patternSet q) (patternSet_definable B q)
  let P : Finset (Fin a.arity) → Set (Fin b.arity → M) := fun p => f '' (a.domain ∩ patternSet p)
  have hP : ∀ p, DefinableOverBase B (fun _ : Fin b.arity => .rv) (P p) := fun p =>
    image_definable B a.domain f hgraph (patternSet p) (patternSet_definable B p)
  have hA : ∀ p, sclass (strip (ofChart a) p) = ∑ q, sclass (strip (inside (ofChart a) (Q q) (hQ q)) p) := by
    intro p
    apply sclass_strip_split (ofChart a) ha Q hQ p
    · intro u hu
      exact ⟨zeroLocus (f u), hu.1,
        mem_patternSet_zeroLocus (f u) (b.domain_definable.proper _ (hbij.mapsTo hu.1))⟩
    · intro u _ i j hi hj
      exact pattern_unique hi.2 hj.2
  have hB : ∀ q, sclass (strip (ofChart b) q) = ∑ p, sclass (strip (inside (ofChart b) (P p) (hP p)) q) := by
    intro q
    apply sclass_strip_split (ofChart b) hb P hP q
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := hbij.surjOn hv.1
      exact ⟨zeroLocus u, u, ⟨hu, mem_patternSet_zeroLocus u (a.domain_definable.proper u hu)⟩, rfl⟩
    · rintro v _ i j ⟨u, hu, rfl⟩ ⟨u', hu', he⟩
      have huu : u' = u := hbij.injOn hu'.1 hu.1 he
      subst huu
      exact pattern_unique hu.2 hu'.2
  have hpq : ∀ p q, sclass (strip (inside (ofChart a) (Q q) (hQ q)) p) =
      sclass (strip (inside (ofChart b) (P p) (hP p)) q) := by
    intro p q
    let X := piece (inside (ofChart a) (Q q) (hQ q)) p
    let Y := piece (inside (ofChart b) (P p) (hP p)) q
    have hXa : X.domain ⊆ a.domain := fun u hu => hu.1.1
    have hbijXY : Set.BijOn f X.domain Y.domain := by
      refine ⟨fun u hu => ⟨⟨hbij.mapsTo hu.1.1, u, ⟨hu.1.1, hu.2⟩, rfl⟩, hu.1.2.2⟩, hbij.injOn.mono hXa, ?_⟩
      rintro v ⟨⟨_, u, hu, rfl⟩, hvq⟩
      exact ⟨u, ⟨⟨hu.1, hu.1, hvq⟩, hu.2⟩, rfl⟩
    have G : Iso X.toChart Y.toChart := mapIso X.toChart Y.toChart f
      (graph_restrict_definable B a.domain X.domain f hXa X.domain_definable hgraph) hbijXY
      (fun u hu => hw u (hXa hu))
    have hXb : DomainBounded (inside (ofChart a) (Q q) (hQ q)).toChart :=
      bounded_mono (E := ofChart a) (fun _ hu => hu.1) ha
    have hYb : DomainBounded (inside (ofChart b) (P p) (hP p)).toChart :=
      bounded_mono (E := ofChart b) (fun _ hu => hu.1) hb
    exact sclass_iso (admissible_strip _ hXb p) (admissible_strip _ hYb q)
      (RVMeasuredIsomorphisms.trans (RVMeasuredIsomorphisms.symm (stripIso _ p))
        (RVMeasuredIsomorphisms.trans G (stripIso _ q)))
  unfold rho
  rw [Finset.sum_congr rfl (fun p _ => hA p), Finset.sum_congr rfl (fun q _ => hB q), Finset.sum_comm]
  exact Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => hpq p q))

/-! #### Products -/

def headPattern {na nb : ℕ} (P : Finset (Fin (nb + na))) : Finset (Fin na) :=
  Finset.univ.filter (fun i => headIndex nb na i ∈ P)

def tailPattern {na nb : ℕ} (P : Finset (Fin (nb + na))) : Finset (Fin nb) :=
  Finset.univ.filter (fun i => tailIndex nb na i ∈ P)

omit [M ⊨ Axioms.ACVF] in
theorem pattern_product {na nb : ℕ} (P : Finset (Fin (nb + na))) (z : Fin (nb + na) → M) :
    z ∈ patternSet P ↔
      z ∘ headIndex nb na ∈ patternSet (headPattern P) ∧ z ∘ tailIndex nb na ∈ patternSet (tailPattern P) := by
  constructor
  · rintro ⟨hs, hz⟩
    refine ⟨⟨fun i => hs _, fun i => ?_⟩, ⟨fun i => hs _, fun i => ?_⟩⟩
    · simp only [headPattern, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
      exact hz _
    · simp only [tailPattern, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
      exact hz _
  · rintro ⟨⟨hs1, hz1⟩, ⟨hs2, hz2⟩⟩
    refine ⟨GammaBoundedProducts.all_coordinates nb na iRV z hs1 hs2,
      GammaBoundedProducts.all_coordinates nb na (fun i => z i = iRVZero ↔ i ∈ P) id (fun i => ?_) (fun i => ?_)⟩
    · have h := hz1 i
      simp only [headPattern, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at h
      exact h
    · have h := hz2 i
      simp only [tailPattern, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at h
      exact h

theorem patternPair_bijective (na nb : ℕ) :
    Function.Bijective (fun P : Finset (Fin (nb + na)) => (headPattern P, tailPattern P)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun P P' h => ?_, ?_⟩
  · have h1 : headPattern P = headPattern P' := congrArg Prod.fst h
    have h2 : tailPattern P = tailPattern P' := congrArg Prod.snd h
    ext i
    refine GammaBoundedProducts.all_coordinates nb na (fun j => j ∈ P ↔ j ∈ P') id (fun j => ?_) (fun j => ?_) i
    · have h := Finset.ext_iff.mp h1 j
      simp only [headPattern, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    · have h := Finset.ext_iff.mp h2 j
      simp only [tailPattern, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
  · simp only [Fintype.card_finset, Fintype.card_prod, Fintype.card_fin, pow_add]
    exact Nat.mul_comm _ _

theorem productPiece_mem {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (P : Finset (Fin (b.arity + a.arity))) (z : Fin (b.arity + a.arity) → M) :
    z ∈ (piece (ofChart (RVMeasuredProduct.product a b)) P).domain ↔
      z ∈ (RVMeasuredProduct.product (piece (ofChart a) (headPattern P)).toChart
        (piece (ofChart b) (tailPattern P)).toChart).domain := by
  change (z ∈ productSet a.domain b.domain ∧ z ∈ patternSet P) ↔
    z ∈ productSet (a.domain ∩ patternSet (headPattern P)) (b.domain ∩ patternSet (tailPattern P))
  rw [pattern_product]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, h3⟩, h2, h4⟩
  · rintro ⟨⟨h1, h3⟩, h2, h4⟩
    exact ⟨⟨h1, h2⟩, h3, h4⟩

/-- The pattern piece of a product is the product of the pattern pieces. -/
def productPieceIso {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (P : Finset (Fin (b.arity + a.arity))) :
    Iso (piece (ofChart (RVMeasuredProduct.product a b)) P).toChart
      (RVMeasuredProduct.product (piece (ofChart a) (headPattern P)).toChart
        (piece (ofChart b) (tailPattern P)).toChart) :=
  coordinateIso _ _ (fun i => i)
    ⟨fun z hz => (productPiece_mem a b P z).mp hz, fun _ _ _ _ h => h,
      fun z hz => ⟨z, (productPiece_mem a b P z).mpr hz, rfl⟩⟩
    (fun _ _ => rfl)

theorem strip_product_class {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (ha : DomainBounded a) (hb : DomainBounded b) (P : Finset (Fin (b.arity + a.arity))) :
    sclass (strip (ofChart (RVMeasuredProduct.product a b)) P) =
      sclass (strip (ofChart a) (headPattern P)) * sclass (strip (ofChart b) (tailPattern P)) := by
  have hAB : DomainBounded (ofChart (RVMeasuredProduct.product a b)).toChart :=
    RVMeasuredProductProperties.product_domain_bounded a b ha hb
  have h1 := admissible_strip (ofChart (RVMeasuredProduct.product a b)) hAB P
  have h2 := admissible_strip (ofChart a) ha (headPattern P)
  have h3 := admissible_strip (ofChart b) hb (tailPattern P)
  rw [sclass_eq h1, sclass_eq h2, sclass_eq h3, ← objectClass_product]
  exact objectClass_iso (RVMeasuredIsomorphisms.trans (RVMeasuredIsomorphisms.symm (stripIso _ P))
    (RVMeasuredIsomorphisms.trans (productPieceIso a b P)
      (RVMeasuredIsomorphisms.productIso (stripIso _ _) (stripIso _ _))))

theorem rho_product {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (ha : DomainBounded a) (hb : DomainBounded b) :
    rho (RVMeasuredProduct.product a b) = rho a * rho b := by
  unfold rho
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_bijective _ (patternPair_bijective a.arity b.arity) _ _
    (fun P => strip_product_class a b ha hb P)

/-! ### The comparison ring maps -/

def fromBoundedInvariant (B : Base (M := M)) : RVBoundedRing.Invariant B (StrictRing B) where
  value _ a := rho a.toChart
  unit := (rho_strict (unit B)).trans (objectClass_unit B)
  product _ _ a b := rho_product a.toChart b.toChart a.domain_bounded b.domain_bounded
  iso _ a b F := rho_iso a.toChart b.toChart a.domain_bounded b.domain_bounded F
  empty _ a h := rho_empty a.toChart h
  scissor _ a b c d h := rho_scissor a.toChart b.toChart c.toChart d.toChart
    a.domain_bounded b.domain_bounded c.domain_bounded d.domain_bounded h

/-- Split every bounded chart by its `∞`-pattern and delete the `∞`-coordinates. -/
def fromBounded (B : Base (M := M)) : RVBoundedRing.Ring B →+* StrictRing B :=
  RVBoundedRing.lift B (fromBoundedInvariant B)

theorem fromBounded_objectClass (B : Base (M := M)) {k : ℕ} (a : RVBoundedCharts.BoundedChart B k) :
    fromBounded B (RVBoundedRing.objectClass a) = rho a.toChart :=
  RVBoundedRing.lift_objectClass B (fromBoundedInvariant B) a

theorem fromBounded_strict (B : Base (M := M)) {k : ℕ} (a : StrictChart B k) :
    fromBounded B (RVBoundedRing.objectClass a.toBoundedChart) = objectClass a :=
  (fromBounded_objectClass B a.toBoundedChart).trans (rho_strict a)

theorem to_from (B : Base (M := M)) : (toBounded B).comp (fromBounded B) = RingHom.id _ := by
  apply RVBoundedGrading.hom_ext B
  intro k a
  change toBounded B (fromBounded B (RVBoundedRing.objectClass a)) = RVBoundedRing.objectClass a
  have hA : DomainBounded (ofChart a.toChart).toChart := a.domain_bounded
  rw [fromBounded_objectClass, rho, map_sum, ← bclass_ofChart a, bclass_pieces _ hA]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hP : DomainBounded (piece (ofChart a.toChart) p).toChart := bounded_mono (fun _ hu => hu.1) hA
  rw [toBounded_sclass (admissible_strip _ hA p)]
  exact (bclass_iso hP (strip_bounded _ hA p) (stripIso _ p)).symm

theorem from_to (B : Base (M := M)) : (fromBounded B).comp (toBounded B) = RingHom.id _ := by
  apply hom_ext B
  intro k a
  change fromBounded B (toBounded B (objectClass a)) = objectClass a
  rw [toBounded_objectClass, fromBounded_strict]

/-- The paper's literal doubly bounded ring (no `∞` coordinates) is isomorphic to the Lean
bounded ring, by the map forgetting infinity-freeness. -/
def equivalence (B : Base (M := M)) : StrictRing B ≃+* RVBoundedRing.Ring B :=
  RingEquiv.ofBijective (toBounded B) ⟨(by
    intro x y h
    have he := congrArg (fromBounded B) h
    exact (RingHom.congr_fun (from_to B) x).symm.trans (he.trans (RingHom.congr_fun (from_to B) y))), (by
    intro y
    exact ⟨fromBounded B y, RingHom.congr_fun (to_from B) y⟩)⟩

theorem equivalence_objectClass (B : Base (M := M)) {k : ℕ} (a : StrictChart B k) :
    equivalence B (objectClass a) = RVBoundedRing.objectClass a.toBoundedChart :=
  toBounded_objectClass B a

theorem equivalence_symm_objectClass (B : Base (M := M)) {k : ℕ} (a : StrictChart B k) :
    (equivalence B).symm (RVBoundedRing.objectClass a.toBoundedChart) = objectClass a := by
  rw [RingEquiv.symm_apply_eq, equivalence_objectClass]

end DiamondIntegral.Section4.RVStrictBoundedComparison
