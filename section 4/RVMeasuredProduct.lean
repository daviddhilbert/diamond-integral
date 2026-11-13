import «section 4».RVRealProducts
import «section 4».RVVolumeMaps

/-! Actual products of measured RV objects. The domain, finite-fibre
coordinate map and partial Gamma volume graph are constructed over the
same base. No category-product or tensor theorem is assumed as an input. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVMeasuredProduct
open RVMeasuredCharts RVRealProducts RVVolumeMaps FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def product {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l) : Chart B (l + k) where
  arity := b.arity + a.arity
  domain := productSet a.domain b.domain
  domain_definable := productSet_definable B _ _ a.domain_definable b.domain_definable
  coordinate := productMap a.coordinate b.coordinate
  coordinate_definable := product_graph_definable B _ _ _ _ a.coordinate_definable b.coordinate_definable
  coordinate_proper := by
    intro u hu
    apply GammaBoundedProducts.all_coordinates l k NonzeroRV (productMap a.coordinate b.coordinate u)
    · intro i
      change NonzeroRV (join l k (a.coordinate (u ∘ headIndex b.arity a.arity))
        (b.coordinate (u ∘ tailIndex b.arity a.arity)) (headIndex l k i))
      rw [join_head]
      exact a.coordinate_proper _ hu.1 i
    · intro i
      change NonzeroRV (join l k (a.coordinate (u ∘ headIndex b.arity a.arity))
        (b.coordinate (u ∘ tailIndex b.arity a.arity)) (tailIndex l k i))
      rw [join_tail]
      exact b.coordinate_proper _ hu.2 i
  finite_fibres := by
    intro t
    let A : Set (Fin a.arity → M) := {x | x ∈ a.domain ∧ a.coordinate x = t ∘ headIndex l k}
    let C : Set (Fin b.arity → M) := {y | y ∈ b.domain ∧ b.coordinate y = t ∘ tailIndex l k}
    have hA : A.Finite := a.finite_fibres _
    have hC : C.Finite := b.finite_fibres _
    have hf : ((fun p : (Fin a.arity → M) × (Fin b.arity → M) => join b.arity a.arity p.1 p.2) ''
        (A ×ˢ C)).Finite := (hA.prod hC).image _
    apply hf.subset
    intro u hu
    have ha : a.coordinate (u ∘ headIndex b.arity a.arity) = t ∘ headIndex l k := by
      have h := congrArg (fun w : Fin (l + k) → M => w ∘ headIndex l k) hu.2
      have hh : productMap a.coordinate b.coordinate u ∘ headIndex l k =
          a.coordinate (u ∘ headIndex b.arity a.arity) :=
        funext (join_head l k (a.coordinate (u ∘ headIndex b.arity a.arity))
          (b.coordinate (u ∘ tailIndex b.arity a.arity)))
      exact hh.symm.trans h
    have hb : b.coordinate (u ∘ tailIndex b.arity a.arity) = t ∘ tailIndex l k := by
      have h := congrArg (fun w : Fin (l + k) → M => w ∘ tailIndex l k) hu.2
      have ht : productMap a.coordinate b.coordinate u ∘ tailIndex l k =
          b.coordinate (u ∘ tailIndex b.arity a.arity) :=
        funext (join_tail l k (a.coordinate (u ∘ headIndex b.arity a.arity))
          (b.coordinate (u ∘ tailIndex b.arity a.arity)))
      exact ht.symm.trans h
    exact ⟨(u ∘ headIndex b.arity a.arity, u ∘ tailIndex b.arity a.arity),
      ⟨⟨hu.1.1, ha⟩, hu.1.2, hb⟩, join_reconstruct b.arity a.arity u⟩
  volume := fun u => a.volume (u ∘ headIndex b.arity a.arity) * b.volume (u ∘ tailIndex b.arity a.arity)
  volume_definable := by
    have hD : DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv) (productSet a.domain b.domain) :=
      productSet_definable B a.domain b.domain a.domain_definable b.domain_definable
    have hA : VolumeDefinable B (productSet a.domain b.domain)
        (fun u => a.volume (u ∘ headIndex b.arity a.arity)) :=
      reindex_restrict_definable B a.domain (productSet a.domain b.domain) hD a.volume a.volume_definable (headIndex b.arity a.arity)
        (fun _ hu => hu.1)
    have hC : VolumeDefinable B (productSet a.domain b.domain)
        (fun u => b.volume (u ∘ tailIndex b.arity a.arity)) :=
      reindex_restrict_definable B b.domain (productSet a.domain b.domain) hD b.volume b.volume_definable (tailIndex b.arity a.arity)
        (fun _ hu => hu.2)
    exact multiply_definable B (productSet a.domain b.domain) hD
      (fun u => a.volume (u ∘ headIndex b.arity a.arity))
      (fun u => b.volume (u ∘ tailIndex b.arity a.arity)) hA hC

theorem product_volume_join {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (x : Fin a.arity → M) (y : Fin b.arity → M) :
    (product a b).volume (join b.arity a.arity x y) = a.volume x * b.volume y := by
  have hh : join b.arity a.arity x y ∘ headIndex b.arity a.arity = x :=
    funext (join_head b.arity a.arity x y)
  have ht : join b.arity a.arity x y ∘ tailIndex b.arity a.arity = y :=
    funext (join_tail b.arity a.arity x y)
  change a.volume (join b.arity a.arity x y ∘ headIndex b.arity a.arity) *
    b.volume (join b.arity a.arity x y ∘ tailIndex b.arity a.arity) = _
  rw [hh, ht]

end DiamondIntegral.Section4.RVMeasuredProduct
