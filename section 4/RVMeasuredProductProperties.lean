import «section 4».RVMeasuredProduct
import «section 4».RVMeasuredBounds
import «section 4».GammaSumMap

/-! Actual measured RV products multiply corrected weights, preserve
finite RES value patterns and preserve doubly bounded domains. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVMeasuredProductProperties
open RVMeasuredCharts RVMeasuredProduct RVMeasuredBounds RVRealProducts
open FiniteTupleBlocks FiniteTupleGraphProduct

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem product_weight_join {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (x : Fin a.arity → M) (y : Fin b.arity → M) :
    (product a b).correctedWeight (join b.arity a.arity x y) = a.correctedWeight x * b.correctedWeight y := by
  have hp : (∏ i, codeValue (join l k (a.coordinate x) (b.coordinate y) i)) =
      (∏ i, codeValue (a.coordinate x i)) * ∏ i, codeValue (b.coordinate y i) := by
    have h := GammaSumMap.prod_blocks l k (fun i => codeValue (join l k (a.coordinate x) (b.coordinate y) i))
    simpa only [join_head, join_tail] using h
  calc
    (product a b).correctedWeight (join b.arity a.arity x y) =
        (a.volume x * b.volume y) * ∏ i, codeValue (join l k (a.coordinate x) (b.coordinate y) i) :=
      congrArg₂ (· * ·) (product_volume_join a b x y)
        (congrArg (fun q : Fin (l + k) → M => ∏ i, codeValue (q i)) (productMap_join a.coordinate b.coordinate x y))
    _ = a.correctedWeight x * b.correctedWeight y := by
      rw [hp]
      change (a.volume x * b.volume y) * ((∏ i, codeValue (a.coordinate x i)) * ∏ i, codeValue (b.coordinate y i)) =
        (a.volume x * ∏ i, codeValue (a.coordinate x i)) * (b.volume y * ∏ i, codeValue (b.coordinate y i))
      ac_rfl

theorem product_pattern {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (u : (product a b).domain) :
    (product a b).valuePattern u = join b.arity a.arity
      (a.valuePattern ⟨u.val ∘ headIndex b.arity a.arity, u.property.1⟩)
      (b.valuePattern ⟨u.val ∘ tailIndex b.arity a.arity, u.property.2⟩) := by
  apply block_ext b.arity a.arity
  · funext i
    change (product a b).valuePattern u (headIndex b.arity a.arity i) =
      join b.arity a.arity
        (a.valuePattern ⟨u.val ∘ headIndex b.arity a.arity, u.property.1⟩)
        (b.valuePattern ⟨u.val ∘ tailIndex b.arity a.arity, u.property.2⟩) (headIndex b.arity a.arity i)
    rw [join_head]
    rfl
  · funext i
    change (product a b).valuePattern u (tailIndex b.arity a.arity i) =
      join b.arity a.arity
        (a.valuePattern ⟨u.val ∘ headIndex b.arity a.arity, u.property.1⟩)
        (b.valuePattern ⟨u.val ∘ tailIndex b.arity a.arity, u.property.2⟩) (tailIndex b.arity a.arity i)
    rw [join_tail]
    rfl

theorem product_finite_patterns {B : Base (M := M)} {k l : ℕ} (a : RESChart B k) (b : RESChart B l) :
    (Set.range (product a.toChart b.toChart).valuePattern).Finite := by
  have hf : ((fun p : (Fin a.arity → Values.GammaTop (M := M)) × (Fin b.arity → Values.GammaTop (M := M)) =>
      join b.arity a.arity p.1 p.2) ''
      ((Set.range a.toChart.valuePattern) ×ˢ (Set.range b.toChart.valuePattern))).Finite :=
    (a.finite_values.prod b.finite_values).image _
  apply hf.subset
  rintro p ⟨u, rfl⟩
  let x : a.domain := ⟨u.val ∘ headIndex b.arity a.arity, u.property.1⟩
  let y : b.domain := ⟨u.val ∘ tailIndex b.arity a.arity, u.property.2⟩
  exact ⟨(a.toChart.valuePattern x, b.toChart.valuePattern y), ⟨⟨x, rfl⟩, y, rfl⟩,
    (product_pattern a.toChart b.toChart u).symm⟩

def resProduct {B : Base (M := M)} {k l : ℕ} (a : RESChart B k) (b : RESChart B l) : RESChart B (l + k) :=
  ⟨product a.toChart b.toChart, product_finite_patterns a b⟩

theorem product_domain_bounded {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (ha : DomainBounded a) (hb : DomainBounded b) : DomainBounded (product a b) := by
  obtain ⟨β, hβ⟩ := ha
  obtain ⟨γ, hγ⟩ := hb
  refine ⟨max β γ, ?_⟩
  intro u hu
  apply GammaBoundedProducts.all_coordinates b.arity a.arity
    (fun t => NonzeroRV t → (max β γ)⁻¹ ≤ codeValue t ∧ codeValue t ≤ max β γ) u
  · intro i hi
    have h := hβ (u ∘ headIndex b.arity a.arity) hu.1 i hi
    exact ⟨(inv_le_inv_iff.mpr (le_max_left β γ)).trans h.1, h.2.trans (le_max_left β γ)⟩
  · intro i hi
    have h := hγ (u ∘ tailIndex b.arity a.arity) hu.2 i hi
    exact ⟨(inv_le_inv_iff.mpr (le_max_right β γ)).trans h.1, h.2.trans (le_max_right β γ)⟩

end DiamondIntegral.Section4.RVMeasuredProductProperties
