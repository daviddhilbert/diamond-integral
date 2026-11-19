import «section 2».PrimitiveDiscs
import Section3.RVOperations

/-! Definitions 7.16 (`rvaffine`), 7.17 (`defn:balance`) and 7.19 (`def:units`),
and Remark 7.18 (`2cell:linear`) in the approved scope: the `∞`-symmetry of
the paradigms and the slope.

The definitions are geometric. Definability over a base is imposed where they
are used. The paradigms `t₁`, `t₂` are elements of `RV_∞`; `t^♯` is the
`rv`-fibre of `t`, which is `{0}` for `t = ∞`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section7.TwoCells
open DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- An open disc of `VF`. -/
def IsOpenDiscVF (D : Set (VF M)) : Prop := IsOpenDisc (Subtype.val '' D)

/-- The fibre `t^♯ = rv⁻¹(t)`. -/
def sharpSet (t : RVInfinity M) : Set (VF M) := {x | rv M x = t}

/-- Definition 7.16: `f` is `vv`-affine on the open disc `D`, with shift `γ`. -/
def VAffine (D : Set (VF M)) (f : VF M → VF M) : Prop :=
  IsOpenDiscVF D ∧ Set.InjOn f D ∧
    ∃ γ : Gamma M, ∀ a ∈ D, ∀ a' ∈ D, vfValue (f a - f a') = γ.val * vfValue (a - a')

/-- Definition 7.16: `f` is `rv`-affine on the open disc `D`, with slope `t`. -/
def HasSlope (D : Set (VF M)) (f : VF M → VF M) (t : RV M) : Prop :=
  ∀ a ∈ D, ∀ a' ∈ D, rv M (f a - f a') = t.val * rv M (a - a')

def RVAffine (D : Set (VF M)) (f : VF M → VF M) : Prop :=
  IsOpenDiscVF D ∧ Set.InjOn f D ∧ ∃ t : RV M, HasSlope D f t

/-- The two projections and the fibres of a subset of `VF²`. -/
def first (A : Set (VF M × VF M)) : Set (VF M) := Prod.fst '' A
def second (A : Set (VF M × VF M)) : Set (VF M) := Prod.snd '' A
def fibre (A : Set (VF M × VF M)) (a : VF M) : Set (VF M) := {b | (a, b) ∈ A}

/-- The disc-to-disc property: open subdiscs go to open discs. -/
def DiscToDisc (D : Set (VF M)) (f : VF M → VF M) : Prop :=
  ∀ E ⊆ D, IsOpenDiscVF E → IsOpenDiscVF (f '' E)

/-- Definition 7.17: `f` is balanced in `A`, with paradigms `t₁`, `t₂`. -/
structure Balanced (A : Set (VF M × VF M)) (f : VF M → VF M) (t₁ t₂ : RVInfinity M) : Prop where
  first_disc : IsOpenDiscVF (first A)
  second_disc : IsOpenDiscVF (second A)
  bijective : Set.BijOn f (first A) (second A)
  discToDisc : DiscToDisc (first A) f
  rvAffine : RVAffine (first A) f
  fibre_eq : ∀ a ∈ first A, fibre A a = (· + f a) '' sharpSet t₂
  preimage_eq : ∀ a ∈ first A, f ⁻¹' fibre A a ∩ first A = (a - ·) '' sharpSet t₁

/-- Definition 7.19: a `1`-cell is a point or an open disc inside one RV-disc. -/
def IsOneCell (D : Set (VF M)) : Prop :=
  (∃ x : VF M, D = {x}) ∨ (IsOpenDiscVF D ∧ ∃ t : RVInfinity M, D ⊆ sharpSet t)

/-- Definition 7.19: the three positioning cases of a `2`-cell. -/
def PositioningCase (A : Set (VF M × VF M)) (ε : VF M → VF M) (t : RV M) : Prop :=
  (∀ a ∈ first A, ∀ a' ∈ first A, ε a = ε a') ∨
    (Set.InjOn ε (first A) ∧ DiscToDisc (first A) ε ∧
      ∃ x : VF M, ∃ γ : Gamma M, Subtype.val '' (ε '' first A) =
        BallImaginaries.underlying (openDiscCode x γ) ∧ Values.vrv t.val ≤ γ.val) ∨
    ∃ t₁ : RVInfinity M, Balanced A ε t₁ t.val

/-- Definition 7.19: a `2`-cell, with positioning function `ε` and paradigm `t`. -/
def IsTwoCell (A : Set (VF M × VF M)) : Prop :=
  (∃ t₁ t₂ : RVInfinity M, ∀ p ∈ A, rv M p.1 = t₁ ∧ rv M p.2 = t₂) ∧ IsOneCell (first A) ∧
    ∃ ε : VF M → VF M, ∃ t : RV M,
      (∀ a ∈ first A, fibre A a = (· + ε a) '' sharpSet t.val) ∧ PositioningCase A ε t

/-! ### Remark 7.18 -/

section Remark
variable {A : Set (VF M × VF M)} {f : VF M → VF M} {t₁ t₂ : RVInfinity M}

theorem sharp_zero : sharpSet (rvZero M) = {(0 : VF M)} := by
  ext x
  simp only [sharpSet, Set.mem_setOf_eq, rv_eq_zero_iff, Set.mem_singleton_iff]

omit hM in
theorem mem_second_of_fibre {a b : VF M} (hb : b ∈ fibre A a) : b ∈ second A := ⟨(a, b), hb, rfl⟩

/-- If `t₂ = ∞`, each fibre is the single point `f(a)`. -/
theorem fibre_of_zero (h : Balanced A f t₁ t₂) (h2 : t₂ = rvZero M) {a : VF M} (ha : a ∈ first A) :
    fibre A a = {f a} := by
  rw [h.fibre_eq a ha, h2, sharp_zero, Set.image_singleton, zero_add]

/-- If `t₁ = ∞`, each fibre is the single point `f(a)`. -/
theorem fibre_of_zero_left (h : Balanced A f t₁ t₂) (h1 : t₁ = rvZero M) {a : VF M} (ha : a ∈ first A) :
    fibre A a = {f a} := by
  have hpre := h.preimage_eq a ha
  rw [h1, sharp_zero, Set.image_singleton, sub_zero] at hpre
  ext b
  constructor
  · intro hb
    obtain ⟨a', ha', rfl⟩ := h.bijective.2.2 (mem_second_of_fibre hb)
    have hmem : a' ∈ f ⁻¹' fibre A a ∩ first A := ⟨hb, ha'⟩
    rw [hpre] at hmem
    rw [Set.mem_singleton_iff.mp hmem]
    rfl
  · intro hb
    rw [Set.mem_singleton_iff.mp hb]
    obtain ⟨s, hs⟩ := rv_surjective t₂
    have hfib := h.fibre_eq a ha
    have hmem : s + f a ∈ fibre A a := by
      rw [hfib]
      exact ⟨s, hs, rfl⟩
    obtain ⟨a', ha', he⟩ := h.bijective.2.2 (mem_second_of_fibre hmem)
    have hm : a' ∈ f ⁻¹' fibre A a ∩ first A := ⟨by rw [Set.mem_preimage, he]; exact hmem, ha'⟩
    rw [hpre] at hm
    rw [Set.mem_singleton_iff.mp hm] at he
    rw [← he] at hmem
    exact hmem

/-- Remark 7.18 (`∞`-symmetry): one paradigm is `∞` exactly when the other is. -/
theorem paradigm_zero_iff (h : Balanced A f t₁ t₂) (hne : (first A).Nonempty) :
    t₁ = rvZero M ↔ t₂ = rvZero M := by
  obtain ⟨a, ha⟩ := hne
  constructor
  · intro h1
    have hfib := fibre_of_zero_left h h1 ha
    obtain ⟨s, hs⟩ := rv_surjective t₂
    have hmem : s + f a ∈ fibre A a := by
      rw [h.fibre_eq a ha]
      exact ⟨s, hs, rfl⟩
    rw [hfib, Set.mem_singleton_iff, add_eq_right] at hmem
    rw [← hs, hmem, rv_zero]
  · intro h2
    have hfib := fibre_of_zero h h2 ha
    have hpre := h.preimage_eq a ha
    rw [hfib] at hpre
    obtain ⟨s, hs⟩ := rv_surjective t₁
    have hmem : a - s ∈ f ⁻¹' {f a} ∩ first A := by
      rw [hpre]
      exact ⟨s, hs, rfl⟩
    have he : a - s = a := h.bijective.2.1 hmem.2 ha hmem.1
    rw [sub_eq_self] at he
    rw [← hs, he, rv_zero]

/-- Remark 7.18: when a paradigm is `∞`, `A` is the graph of `f`. -/
theorem graph_of_zero (h : Balanced A f t₁ t₂) (h2 : t₂ = rvZero M) :
    A = {p | p.1 ∈ first A ∧ p.2 = f p.1} := by
  ext p
  constructor
  · intro hp
    have ha : p.1 ∈ first A := ⟨p, hp, rfl⟩
    have hb : p.2 ∈ fibre A p.1 := hp
    rw [fibre_of_zero h h2 ha] at hb
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    change p.2 ∈ fibre A p.1
    rw [fibre_of_zero h h2 ha]
    exact hb

/-- Remark 7.18 (slope): for finite paradigms, every slope `s` of `f` satisfies
`s · t₁ = -t₂`, that is, `s = -t₂/t₁`. -/
theorem slope_eq (h : Balanced A f t₁ t₂) (hne : (first A).Nonempty) {s : RV M}
    (hs : HasSlope (first A) f s) : s.val * t₁ = rv M (-1) * t₂ := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨s₂, hs₂⟩ := rv_surjective t₂
  have hmem : s₂ + f a ∈ fibre A a := by
    rw [h.fibre_eq a ha]
    exact ⟨s₂, hs₂, rfl⟩
  obtain ⟨a', ha', he⟩ := h.bijective.2.2 (mem_second_of_fibre hmem)
  have hpre : a' ∈ f ⁻¹' fibre A a ∩ first A := ⟨by rw [Set.mem_preimage, he]; exact hmem, ha'⟩
  rw [h.preimage_eq a ha] at hpre
  obtain ⟨s₁, hs₁, hs₁e⟩ := hpre
  have hslope := hs a' ha' a ha
  rw [he, add_sub_cancel_right, ← hs₁e, sub_sub_cancel_left] at hslope
  have hneg : rv M (-s₁) = rv M (-1) * rv M s₁ := by
    change RVOperations.rvHom (-s₁) = RVOperations.rvHom (-1) * RVOperations.rvHom s₁
    rw [← map_mul, neg_one_mul]
  have hsq : rv M (-1) * rv M (-1) = 1 := by
    change RVOperations.rvHom (-1) * RVOperations.rvHom (-1) = 1
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [hneg, hs₂, hs₁] at hslope
  calc s.val * t₁ = (rv M (-1) * rv M (-1)) * (s.val * t₁) := by rw [hsq, one_mul]
    _ = rv M (-1) * (s.val * (rv M (-1) * t₁)) := by rw [mul_assoc, mul_left_comm (rv M (-1)) s.val t₁]
    _ = rv M (-1) * t₂ := by rw [← hslope]

end Remark

end DiamondIntegral.Section7.TwoCells
