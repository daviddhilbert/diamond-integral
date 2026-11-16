import «section 6».FreezingDomains
import «section 6».FiniteOpenCenterGraphs

/-! Simultaneous freezing on a finite disjoint family. Every use carries
the product-domain proof for its actual current function domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical Filter Topology

namespace DiamondIntegral.Section6.FMT

variable {I X Y Z : Type*}

def familyFreeze (D : I → Set X) (c : I → X) (x : X) : X :=
  if h : ∃ i, x ∈ D i then c h.choose else x

theorem familyFreeze_inside (D : I → Set X) (c : I → X)
    (hsep : ∀ i j x, x ∈ D i → x ∈ D j → i = j)
    (i : I) (x : X) (hx : x ∈ D i) : familyFreeze D c x = c i := by
  have h : ∃ j, x ∈ D j := ⟨i,hx⟩
  rw [familyFreeze,dif_pos h,hsep h.choose i x h.choose_spec hx]

theorem familyFreeze_outside (D : I → Set X) (c : I → X)
    (x : X) (hx : ∀ i, x ∉ D i) : familyFreeze D c x = x := by
  rw [familyFreeze,dif_neg (not_exists.mpr hx)]

theorem familyFreeze_mem_same (D : I → Set X) (c : I → X)
    (hsep : ∀ i j x, x ∈ D i → x ∈ D j → i = j)
    (hc : ∀ i, c i ∈ D i) (i : I) (x : X) :
    familyFreeze D c x ∈ D i ↔ x ∈ D i := by
  by_cases hx : ∃ j, x ∈ D j
  · obtain ⟨j,hj⟩ := hx
    rw [familyFreeze_inside D c hsep j x hj]
    constructor
    · intro hi
      exact hsep j i (c j) (hc j) hi ▸ hj
    · intro hi
      exact hsep j i x hj hi ▸ hc j
  · rw [familyFreeze_outside D c x (not_exists.mp hx)]

theorem familyFreeze_idempotent (D : I → Set X) (c : I → X)
    (hsep : ∀ i j x, x ∈ D i → x ∈ D j → i = j)
    (hc : ∀ i, c i ∈ D i) (x : X) :
    familyFreeze D c (familyFreeze D c x) = familyFreeze D c x := by
  by_cases hx : ∃ i, x ∈ D i
  · obtain ⟨i,hi⟩ := hx
    rw [familyFreeze_inside D c hsep i x hi,familyFreeze_inside D c hsep i (c i) (hc i)]
  · rw [familyFreeze_outside D c x (not_exists.mp hx),familyFreeze_outside D c x (not_exists.mp hx)]

variable [TopologicalSpace X]

theorem familyFreeze_continuous [Finite I] (D : I → Set X) (c : I → X)
    (hsep : ∀ i j x, x ∈ D i → x ∈ D j → i = j)
    (hcl : ∀ i, IsClopen (D i)) : Continuous (familyFreeze D c) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : ∃ i, x ∈ D i
  · obtain ⟨i,hi⟩ := hx
    apply (continuousAt_const (y := c i)).congr_of_eventuallyEq
    filter_upwards [(hcl i).isOpen.mem_nhds hi] with y hy
    exact familyFreeze_inside D c hsep i y hy
  · apply continuousAt_id.congr_of_eventuallyEq
    have ho : IsOpen (⋃ i, D i)ᶜ := (isClopen_iUnion_of_finite hcl).isClosed.isOpen_compl
    have hm : x ∈ (⋃ i, D i)ᶜ := by simpa only [Set.mem_compl_iff,Set.mem_iUnion] using hx
    filter_upwards [ho.mem_nhds hm] with y hy
    apply familyFreeze_outside
    simpa only [Set.mem_compl_iff,Set.mem_iUnion,not_exists] using hy

def familyFreezePoint (D : I → Set X) (c : I → X) (p : X × Y) : X × Y :=
  (familyFreeze D c p.1,p.2)

theorem familyFreezePoint_mapsTo (A : Set (X × Y)) (D : I → Set X) (c : I → X)
    (hprod : ∀ i, ProductDomain A (D i) (c i)) : Set.MapsTo (familyFreezePoint D c) A A := by
  intro p hp
  by_cases hx : ∃ i, p.1 ∈ D i
  · change (familyFreeze D c p.1,p.2) ∈ A
    rw [familyFreeze,dif_pos hx]
    exact (hprod hx.choose p.1 hx.choose_spec p.2).mp hp
  · simpa only [familyFreezePoint,familyFreeze,dif_neg hx,Prod.mk.eta] using hp

def familyFreezeFunction {A : Set (X × Y)} (D : I → Set X) (c : I → X)
    (hprod : ∀ i, ProductDomain A (D i) (c i)) (f : A → Z) (p : A) : Z :=
  f ⟨familyFreezePoint D c p.val,familyFreezePoint_mapsTo A D c hprod p.property⟩

theorem familyFreezeFunction_inside {A : Set (X × Y)} (D : I → Set X) (c : I → X)
    (hsep : ∀ i j x, x ∈ D i → x ∈ D j → i = j)
    (hprod : ∀ i, ProductDomain A (D i) (c i)) (f : A → Z)
    (p : A) (i : I) (hp : p.val.1 ∈ D i) :
    familyFreezeFunction D c hprod f p =
      f ⟨(c i,p.val.2),(hprod i p.val.1 hp p.val.2).mp p.property⟩ := by
  unfold familyFreezeFunction
  congr 1
  apply Subtype.ext
  exact congrArg (fun x => (x,p.val.2)) (familyFreeze_inside D c hsep i p.val.1 hp)

variable [TopologicalSpace Y] [TopologicalSpace Z]

theorem familyFreezeFunction_continuous [Finite I] {A : Set (X × Y)}
    (D : I → Set X) (c : I → X)
    (hsep : ∀ i j x, x ∈ D i → x ∈ D j → i = j)
    (hcl : ∀ i, IsClopen (D i))
    (hprod : ∀ i, ProductDomain A (D i) (c i)) (f : A → Z) (hf : Continuous f) :
    Continuous (familyFreezeFunction D c hprod f) := by
  have hp : Continuous (familyFreezePoint D c : X × Y → X × Y) :=
    ((familyFreeze_continuous D c hsep hcl).comp continuous_fst).prodMk continuous_snd
  exact hf.comp ((hp.comp continuous_subtype_val).subtype_mk
    (fun p : A => familyFreezePoint_mapsTo A D c hprod p.property))

end DiamondIntegral.Section6.FMT
