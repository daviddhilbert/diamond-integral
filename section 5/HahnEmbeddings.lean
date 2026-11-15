import Mathlib.RingTheory.HahnSeries.Basic

/-! Composition of actual exponent embeddings, used for the finite
Laurent levels inside one Puiseux field. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open HahnSeries
variable {Γ Γ' Γ'' k : Type*} [PartialOrder Γ] [PartialOrder Γ'] [PartialOrder Γ''] [Zero k]

theorem hahnEmbDomain_comp (f : Γ ↪o Γ') (g : Γ' ↪o Γ'') (x : HahnSeries Γ k) :
    embDomain g (embDomain f x) = embDomain (f.trans g) x := by
  ext z
  by_cases hz : z ∈ Set.range g
  · obtain ⟨y, rfl⟩ := hz
    rw [embDomain_coeff]
    by_cases hy : y ∈ Set.range f
    · obtain ⟨a, rfl⟩ := hy
      change (embDomain f x).coeff (f a) =
        (embDomain (f.trans g) x).coeff ((f.trans g) a)
      rw [embDomain_coeff, embDomain_coeff]
    · rw [embDomain_of_notMem_range hy]
      symm
      apply embDomain_of_notMem_range
      rintro ⟨a, ha⟩
      exact hy ⟨a, g.injective ha⟩
  · rw [embDomain_of_notMem_range hz]
    symm
    apply embDomain_of_notMem_range
    rintro ⟨a, ha⟩
    exact hz ⟨f a, ha⟩


section LinearOrder
variable {A B R : Type*} [LinearOrder A] [LinearOrder B] [Zero A] [Zero B] [Zero R]

theorem hahnEmbDomain_order (f : A ↪o B) (x : HahnSeries A R) (hx : x ≠ 0) :
    (embDomain f x).order = f x.order := by
  have he : embDomain f x ≠ 0 := fun h => hx (embDomain_injective (h.trans embDomain_zero.symm))
  have ho := orderTop_embDomain (f := f) (x := x)
  rw [← order_eq_orderTop_of_ne_zero he, ← order_eq_orderTop_of_ne_zero hx, WithTop.map_coe] at ho
  exact WithTop.coe_injective ho

theorem hahnEmbDomain_leadingCoeff (f : A ↪o B) (x : HahnSeries A R) (hx : x ≠ 0) :
    (embDomain f x).leadingCoeff = x.leadingCoeff := by
  rw [leadingCoeff_eq, hahnEmbDomain_order f x hx, embDomain_coeff, ← leadingCoeff_eq]

end LinearOrder

end DiamondIntegral.Section5
