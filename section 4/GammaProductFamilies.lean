import «section 4».GammaPrefixIntegration
import «section 4».GammaIntegralCongruence

/-! Products of actual integer families and multiplicativity of their
finite-dimensional Euler integrals. The proof uses actual fibre evaluation
and additivity, with no product-integral axiom. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaProductFamilies
open GammaFamilyIntegration GammaIntegerFamilies GammaIteratedIntegral GammaCoordinatePullback
open GammaPrefixIntegration GammaIntegralCongruence GammaBlockSlices GammaParameterExtension FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def extendFamily (B : Base (M := M)) (C : Set (Values.Gamma (M := M))) {n : ℕ}
    (f : familySubgroup B n) : familySubgroup (GammaBaseExtension.withGamma B C) n :=
  ⟨f.val, ⟨f.property.1, fun a => GammaBaseExtension.gammaRelation_extend B C (f.property.2 a)⟩⟩

def productFamily (B : Base (M := M)) {n m : ℕ} (f : familySubgroup B m) (g : familySubgroup B n) :
    familySubgroup B (n + m) :=
  ⟨(fun z => f.val (z ∘ headIndex n m) * g.val (z ∘ tailIndex n m)),
    combine_definable B _ _ (reindex_definable B f.val f.property (headIndex n m))
      (reindex_definable B g.val g.property (tailIndex n m)) (fun a b => a * b)⟩

theorem productFamily_join (B : Base (M := M)) {n m : ℕ}
    (f : familySubgroup B m) (g : familySubgroup B n)
    (u : Fin m → Values.Gamma (M := M)) (y : Fin n → Values.Gamma (M := M)) :
    (productFamily B f g).val (join n m u y) = f.val u * g.val y := by
  have hh : join n m u y ∘ headIndex n m = u := funext (join_head n m u y)
  have ht : join n m u y ∘ tailIndex n m = y := funext (join_tail n m u y)
  change f.val (join n m u y ∘ headIndex n m) * g.val (join n m u y ∘ tailIndex n m) = _
  rw [hh, ht]

theorem prefix_product (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n m : ℕ) (f : familySubgroup B m) (g : familySubgroup B n) :
    integratePrefix h00 hκ hs B hr hγ k n m (productFamily B f g) =
      (integrateAll h00 hκ hs B hr hγ k m f) • g := by
  apply Subtype.ext
  funext y
  rw [integratePrefix_fibre]
  let B' := GammaBaseExtension.withGamma B (Set.range y)
  have hγ' : Cardinal.mk B'.gamma < κ := finite_gamma_extension_small hκ B hγ y
  let f' := extendFamily B (Set.range y) f
  let q : familySubgroup B' m :=
    ⟨slice (productFamily B f g).val y,
      slice_definable B n m (productFamily B f g).val (productFamily B f g).property y⟩
  have he : q = (g.val y) • f' := by
    apply Subtype.ext
    funext u
    change (productFamily B f g).val (join n m u y) = (g.val y) • f.val u
    rw [productFamily_join]
    simp only [zsmul_eq_mul, Int.cast_id, mul_comm]
  have hbase : integrateAll h00 hκ hs B' hr hγ' k m f' = integrateAll h00 hκ hs B hr hγ k m f :=
    integrateAll_congr h00 hκ hs B' B hr hγ' hr hγ k m f' f (fun _ => rfl)
  change integrateAll h00 hκ hs B' hr hγ' k m q =
    (integrateAll h00 hκ hs B hr hγ k m f) • g.val y
  rw [he, map_zsmul, hbase]
  simp only [zsmul_eq_mul, Int.cast_id, mul_comm]

theorem integrateAll_product (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n m : ℕ) (f : familySubgroup B m) (g : familySubgroup B n) :
    integrateAll h00 hκ hs B hr hγ k (n + m) (productFamily B f g) =
      integrateAll h00 hκ hs B hr hγ k m f * integrateAll h00 hκ hs B hr hγ k n g := by
  have h := congrArg (fun H => H (productFamily B f g)) (integrateAll_factor h00 hκ hs B hr hγ k n m)
  change integrateAll h00 hκ hs B hr hγ k (n + m) (productFamily B f g) =
    integrateAll h00 hκ hs B hr hγ k n (integratePrefix h00 hκ hs B hr hγ k n m (productFamily B f g)) at h
  rw [h, prefix_product, map_zsmul]
  simp only [zsmul_eq_mul, Int.cast_id]

end DiamondIntegral.Section4.GammaProductFamilies
