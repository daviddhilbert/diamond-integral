import «section 3».FiniteColumnPartition
import Section4.FiniteCover
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3

theorem finite_columns_of_finite_tests {X Y : Type} (R : Y → X → Prop) (A : Set X)
    (T : Finset Y) (hsep : ∀ x ∈ A, ∀ u ∈ A,
      (∀ y ∈ T, R y x ↔ R y u) → relationColumn R x = relationColumn R u) :
    (relationColumn R '' A).Finite := by
  classical
  let f (x : X) : T → Bool := fun y => decide (R y.val x)
  have heq : ∀ x ∈ A, ∀ u ∈ A, f x = f u → relationColumn R x = relationColumn R u := by
    intro x hx u hu he
    apply hsep x hx u hu
    intro y hy
    exact decide_eq_decide.mp (congrFun he (⟨y,hy⟩ : T))
  let C := relationColumn R '' A
  have hchoice (c : C) : ∃ x ∈ A, relationColumn R x = c.val := c.property
  choose x hx hxc using hchoice
  have hinj : Function.Injective (fun c : C => f (x c)) := by
    intro c d he
    apply Subtype.ext
    exact (hxc c).symm.trans ((heq (x c) (hx c) (x d) (hx d) he).trans (hxc d))
  exact Set.finite_coe_iff.mp (Finite.of_injective _ hinj)

def columnSeparation {α M Y : Type} (R : Y → (α → M) → Prop) (y : Y) : Set (α ⊕ α → M) :=
  {z | ¬ (R y (z ∘ Sum.inl) ↔ R y (z ∘ Sum.inr))}

/-- Saturation makes old-ground definable separating tests finite.
The relation may have an arbitrary interpreted parameter sort. -/
theorem finite_columns_of_definable_separating_tests
    {M α Y : Type} [LRV.Structure M] [Finite α]
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (R : Y → (α → M) → Prop) (A : Set (α → M))
    (hbad : S.Definable LRV {z : α ⊕ α → M | z ∘ Sum.inl ∈ A ∧ z ∘ Sum.inr ∈ A ∧
      relationColumn R (z ∘ Sum.inl) ≠ relationColumn R (z ∘ Sum.inr)})
    (T : Set Y) (htest : ∀ y ∈ T, S.Definable LRV {x | R y x})
    (hsep : ∀ x ∈ A, ∀ u ∈ A, relationColumn R x ≠ relationColumn R u →
      ∃ y ∈ T, ¬ (R y x ↔ R y u)) : (relationColumn R '' A).Finite := by
  classical
  let C := columnSeparation R '' T
  have hC : ∀ c ∈ C, S.Definable LRV c := by
    rintro c ⟨y,hy,rfl⟩
    have hl := (htest y hy).preimage_comp (Sum.inl : α → α ⊕ α)
    have hr := (htest y hy).preimage_comp (Sum.inr : α → α ⊕ α)
    convert ((hl.inter hr).union (hl.compl.inter hr.compl)).compl using 1
    ext z
    change (¬ (R y (z ∘ Sum.inl) ↔ R y (z ∘ Sum.inr))) ↔
      ¬ ((R y (z ∘ Sum.inl) ∧ R y (z ∘ Sum.inr)) ∨ (¬ R y (z ∘ Sum.inl) ∧ ¬ R y (z ∘ Sum.inr)))
    tauto
  have hcov : ∀ z ∈ {z : α ⊕ α → M | z ∘ Sum.inl ∈ A ∧ z ∘ Sum.inr ∈ A ∧
      relationColumn R (z ∘ Sum.inl) ≠ relationColumn R (z ∘ Sum.inr)}, ∃ c ∈ C, z ∈ c := by
    intro z hz
    obtain ⟨y,hy,hxy⟩ := hsep _ hz.1 _ hz.2.1 hz.2.2
    exact ⟨columnSeparation R y,⟨y,hy,rfl⟩,hxy⟩
  obtain ⟨C₀,hC₀,hsub,hcover⟩ := definable_finite_subcover_index hs S hsmall _ hbad C hC hcov
  have hch (c : C₀) : ∃ y ∈ T, columnSeparation R y = c.val := hsub c.property
  choose y hy hye using hch
  letI := hC₀.fintype
  apply finite_columns_of_finite_tests R A (Finset.univ.image y)
  intro x hx u hu he
  by_contra hn
  let z : α ⊕ α → M := Sum.elim x u
  have hz : z ∈ {z : α ⊕ α → M | z ∘ Sum.inl ∈ A ∧ z ∘ Sum.inr ∈ A ∧
      relationColumn R (z ∘ Sum.inl) ≠ relationColumn R (z ∘ Sum.inr)} := ⟨hx,hu,hn⟩
  obtain ⟨c,hc,hzc⟩ := hcover z hz
  let ci : C₀ := ⟨c,hc⟩
  have hbadc : ¬ (R (y ci) x ↔ R (y ci) u) := by
    change z ∈ columnSeparation R (y ci)
    rw [hye ci]
    exact hzc
  exact hbadc (he _ (Finset.mem_image.mpr ⟨ci,Finset.mem_univ _,rfl⟩))
end DiamondIntegral.Section3
