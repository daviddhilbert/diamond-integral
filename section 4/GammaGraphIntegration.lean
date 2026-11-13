import «section 4».GammaPrefixIntegration
import «section 4».FiniteTupleRotation

/-! The integral over the singleton output of an actual Gamma graph is
its weight. This supplies the graph calculation for arbitrary-dimensional
pushforward to Gamma. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaGraphIntegration
open GammaDefinableEuler GammaOrderLogic GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies
open GammaIteratedIntegral GammaIndicators EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem integralFirst_singleton (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    {n : ℕ} (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) (c : Values.Gamma (M := M)) (w : ℤ)
    (he : ∀ a, f (Fin.cons a y) = if a = c then w else 0) :
    integralFirst h00 B k f hf y = w := by
  have hF : fibreFunction h00 B k f hf y = w • point k (toPaperGamma c) := by
    apply eval_injective k
    funext x
    obtain ⟨a, rfl⟩ := toPaperGamma.surjective x
    change fibreFunction h00 B k f hf y (toPaperGamma a) =
      (w • point k (toPaperGamma c)) (toPaperGamma a)
    rw [fibreFunction_eval, he, eval_zsmul, point_eval]
    simp only [toPaperGamma.injective.eq_iff, zsmul_eq_mul, Int.cast_id]
    split_ifs <;> simp
  rw [integralFirst, hF, map_zsmul, totalEuler_point]
  simp

def graphWeight (B : Base (M := M)) {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) : familySubgroup B (n + 1) :=
  ⟨(fun z => f.val (Fin.tail z) * if z 0 = T (Fin.tail z) then 1 else 0),
    by
      change IntegerFamilyDefinable B _
      convert combine_definable B _ _ (reindex_definable B f.val f.property Fin.succ)
        (indicator_definable B _ hT) (fun a b => a * b) using 1
      funext z
      have he : Fin.tail z = z ∘ Fin.succ := by funext i; rfl
      by_cases h : z 0 = T (Fin.tail z) <;>
        simp only [Set.mem_ofPred_eq, h, ite_true, ite_false] <;> rw [he]⟩

def graphWeightMap (B : Base (M := M)) {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)}) :
    familySubgroup B n →+ familySubgroup B (n + 1) where
  toFun := graphWeight B T hT
  map_zero' := by
    apply Subtype.ext
    funext z
    change (0 : ℤ) * _ = 0
    exact zero_mul _
  map_add' f g := by
    apply Subtype.ext
    funext z
    change (f.val (Fin.tail z) + g.val (Fin.tail z)) * _ =
      f.val (Fin.tail z) * _ + g.val (Fin.tail z) * _
    exact add_mul _ _ _

theorem graphWeight_fibre (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    {n : ℕ} (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) (y : Fin n → Values.Gamma (M := M)) :
    integralFirst h00 B k (graphWeight B T hT f).val (graphWeight B T hT f).property y = f.val y := by
  apply integralFirst_singleton h00 B k _ _ y (T y) (f.val y)
  intro a
  change f.val y * (if a = T y then 1 else 0) = if a = T y then f.val y else 0
  split_ifs <;> simp

theorem integrate_graphWeight (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) :
    integrateAll h00 hκ hs B hr hγ k (n + 1) (graphWeight B T hT f) =
      integrateAll h00 hκ hs B hr hγ k n f := by
  have he : integrateFirst h00 hκ hs B hr hγ k n (graphWeight B T hT f) = f := by
    apply Subtype.ext
    funext y
    exact graphWeight_fibre h00 B k T hT f y
  change integrateAll h00 hκ hs B hr hγ k n _ = _
  rw [he]

end DiamondIntegral.Section4.GammaGraphIntegration
