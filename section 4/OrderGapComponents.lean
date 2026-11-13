import «section 4».FiniteOrderComponents
import Mathlib.Data.Set.Basic

/-! Distinct boundary-free gaps with endpoints in the same ordered set
are disjoint. Missing endpoints describe rays and the whole line. The
proof uses the unique greatest boundary below, and least boundary above,
any common interior point; no topology or finite enumeration is needed. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.OrderGapComponents
variable {α : Type*} [LinearOrder α]

def LowerBound (lo : Option α) (x : α) : Prop := lo.elim True (fun a => a < x)
def UpperBound (hi : Option α) (x : α) : Prop := hi.elim True (fun b => x < b)
def gap (lo hi : Option α) : Set α := {x | LowerBound lo x ∧ UpperBound hi x}

structure Valid (A : Set α) (lo hi : Option α) : Prop where
  lower_mem : ∀ a, lo = some a → a ∈ A
  upper_mem : ∀ b, hi = some b → b ∈ A
  no_boundary : ∀ x ∈ A, x ∉ gap lo hi

def GreatestOption (S : Set α) : Option α → Prop
  | none => S = ∅
  | some a => a ∈ S ∧ ∀ x ∈ S, x ≤ a

def LeastOption (S : Set α) : Option α → Prop
  | none => S = ∅
  | some a => a ∈ S ∧ ∀ x ∈ S, a ≤ x

theorem greatest_unique (S : Set α) (lo hi : Option α)
    (hlo : GreatestOption S lo) (hhi : GreatestOption S hi) : lo = hi := by
  cases lo with
  | none =>
    cases hi with
    | none => rfl
    | some b => exact (Set.notMem_empty b (hlo ▸ hhi.1)).elim
  | some a =>
    cases hi with
    | none => exact (Set.notMem_empty a (hhi ▸ hlo.1)).elim
    | some b => exact congrArg some (le_antisymm (hhi.2 a hlo.1) (hlo.2 b hhi.1))

theorem least_unique (S : Set α) (lo hi : Option α)
    (hlo : LeastOption S lo) (hhi : LeastOption S hi) : lo = hi := by
  cases lo with
  | none =>
    cases hi with
    | none => rfl
    | some b => exact (Set.notMem_empty b (hlo ▸ hhi.1)).elim
  | some a =>
    cases hi with
    | none => exact (Set.notMem_empty a (hhi ▸ hlo.1)).elim
    | some b => exact congrArg some (le_antisymm (hlo.2 b hhi.1) (hhi.2 a hlo.1))

theorem upperBound_mono {hi : Option α} {x y : α} (hxy : x ≤ y) (hy : UpperBound hi y) : UpperBound hi x := by
  cases hi with
  | none => trivial
  | some b => exact hxy.trans_lt hy

theorem lowerBound_mono {lo : Option α} {x y : α} (hxy : x ≤ y) (hx : LowerBound lo x) : LowerBound lo y := by
  cases lo with
  | none => trivial
  | some a => exact hx.trans_le hxy

theorem greatest_below (A : Set α) (lo hi : Option α) (hv : Valid A lo hi)
    (x : α) (hx : x ∈ gap lo hi) : GreatestOption {a | a ∈ A ∧ a < x} lo := by
  cases lo with
  | none =>
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact hv.no_boundary a ha.1 ⟨trivial, upperBound_mono ha.2.le hx.2⟩
  | some a =>
    refine ⟨⟨hv.lower_mem a rfl, hx.1⟩, ?_⟩
    intro b hb
    by_contra hba
    have hab : a < b := lt_of_not_ge hba
    exact hv.no_boundary b hb.1 ⟨hab, upperBound_mono hb.2.le hx.2⟩

theorem least_above (A : Set α) (lo hi : Option α) (hv : Valid A lo hi)
    (x : α) (hx : x ∈ gap lo hi) : LeastOption {a | a ∈ A ∧ x < a} hi := by
  cases hi with
  | none =>
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact hv.no_boundary a ha.1 ⟨lowerBound_mono ha.2.le hx.1, trivial⟩
  | some b =>
    refine ⟨⟨hv.upper_mem b rfl, hx.2⟩, ?_⟩
    intro a ha
    by_contra hba
    have hab : a < b := lt_of_not_ge hba
    exact hv.no_boundary a ha.1 ⟨lowerBound_mono ha.2.le hx.1, hab⟩

theorem endpoints_eq_of_inter (A : Set α) (lo hi lo' hi' : Option α)
    (hv : Valid A lo hi) (hv' : Valid A lo' hi') (x : α)
    (hx : x ∈ gap lo hi) (hx' : x ∈ gap lo' hi') : lo = lo' ∧ hi = hi' :=
  ⟨greatest_unique _ lo lo' (greatest_below A lo hi hv x hx) (greatest_below A lo' hi' hv' x hx'),
    least_unique _ hi hi' (least_above A lo hi hv x hx) (least_above A lo' hi' hv' x hx')⟩

theorem disjoint_of_ne (A : Set α) (lo hi lo' hi' : Option α)
    (hv : Valid A lo hi) (hv' : Valid A lo' hi') (hne : (lo, hi) ≠ (lo', hi')) :
    Disjoint (gap lo hi) (gap lo' hi') := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨hl, hu⟩ := endpoints_eq_of_inter A lo hi lo' hi' hv hv' x hx hx'
  exact hne (Prod.ext hl hu)

end DiamondIntegral.Section4.OrderGapComponents
