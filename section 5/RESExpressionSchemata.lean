import «section 5».RESSetSumClasses
import «section 5».RESSetProductClasses

/-! Finite native RES expressions retain literal empty, tagged-sum and
product domains. Their native class is evaluated from the actual leaves. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

def RESSetSchema.empty (B : Base (M := M)) (p : ℕ) (sp : Fin p → SortTag) : RESSetSchema B p 0 sp :=
  ⟨⟨∅, DefinableOverBase.empty B _⟩, 0⟩

theorem RESSetSchema.empty_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i)) : (RESSetSchema.empty B p sp).Valid hc z := by
  apply ((RESSetSchema.empty B p sp).valid_iff_finite_values hc z).mpr
  have he : (RESSetSchema.empty B p sp).rowDomain z = ∅ := rfl
  rw [he, Set.image_empty]
  exact ⟨hz, Set.finite_empty, by simp [empty]⟩

inductive RESExpressionSchema (B : Base (M := M)) (p : ℕ) (sp : Fin p → SortTag) : ℕ → Type where
  | atom {a : ℕ} (object : RESSetSchema B p a sp) : RESExpressionSchema B p sp a
  | empty : RESExpressionSchema B p sp 0
  | sum {a b : ℕ} (left : RESExpressionSchema B p sp a) (right : RESExpressionSchema B p sp b) :
      RESExpressionSchema B p sp (1+(a+b))
  | product {a b : ℕ} (left : RESExpressionSchema B p sp a) (right : RESExpressionSchema B p sp b) :
      RESExpressionSchema B p sp (b+a)

def RESExpressionSchema.setSchema : {a : ℕ} → RESExpressionSchema B p sp a → RESSetSchema B p a sp
  | _, .atom F => F
  | _, .empty => RESSetSchema.empty B p sp
  | _, .sum F G => F.setSchema.sum G.setSchema
  | _, .product F G => F.setSchema.product G.setSchema

def RESExpressionSchema.Valid (hc : CanonicalStructure.IsCanonical (M := M)) :
    {a : ℕ} → RESExpressionSchema B p sp a → (Fin p → M) → Prop
  | _, .atom F, z => F.Valid hc z
  | _, .empty, z => ∀ i, sortEval (sp i) (z i)
  | _, .sum F G, z => F.Valid hc z ∧ G.Valid hc z
  | _, .product F G, z => F.Valid hc z ∧ G.Valid hc z

theorem RESExpressionSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {a : ℕ} (E : RESExpressionSchema B p sp a) : DefinableOverBase B sp {z | E.Valid hc z} := by
  induction E with
  | atom F => exact F.valid_definable hc
  | empty => exact real_definableOverBase B sp _ (sortedUniverse_definable B.real sp)
  | sum F G ihF ihG => exact ihF.inter ihG
  | product F G ihF ihG => exact ihF.inter ihG

theorem RESExpressionSchema.setSchema_valid (hc : CanonicalStructure.IsCanonical (M := M))
    {a : ℕ} (E : RESExpressionSchema B p sp a) (z : Fin p → M) (h : E.Valid hc z) :
    E.setSchema.Valid hc z := by
  induction E with
  | atom F => exact h
  | empty => exact RESSetSchema.empty_valid hc z h
  | sum F G ihF ihG => exact F.setSchema.sum_valid hc G.setSchema z (ihF h.1) (ihG h.2)
  | product F G ihF ihG => exact F.setSchema.product_valid hc G.setSchema z (ihF h.1) (ihG h.2)

def RESExpressionSchema.nativeValue (hc : CanonicalStructure.IsCanonical (M := M))
    (z : Fin p → M) : {a : ℕ} → (E : RESExpressionSchema B p sp a) → E.Valid hc z →
      RESDimensionFreeReduction.Ring ⟨B.real ∪ Set.range z, B.gamma⟩
  | _, .atom F, h => nativeRESChartClass (F.chart hc z h)
  | _, .empty, _ => 0
  | _, .sum F G, h => F.nativeValue hc z h.1 + G.nativeValue hc z h.2
  | _, .product F G, h => F.nativeValue hc z h.1 * G.nativeValue hc z h.2

theorem RESExpressionSchema.nativeClass_eq (hc : CanonicalStructure.IsCanonical (M := M))
    {a : ℕ} (E : RESExpressionSchema B p sp a) (z : Fin p → M) (h : E.Valid hc z) :
    nativeRESChartClass (E.setSchema.chart hc z (E.setSchema_valid hc z h)) = E.nativeValue hc z h := by
  induction E with
  | atom F => rfl
  | empty =>
    apply nativeRESChartClass_empty
    rw [RESSetSchema.chart_domain]
    rfl
  | sum F G ihF ihG =>
    exact (F.setSchema.sum_native_class hc G.setSchema z (F.setSchema_valid hc z h.1)
      (G.setSchema_valid hc z h.2)).trans (congrArg₂ (fun x y => x+y) (ihF h.1) (ihG h.2))
  | product F G ihF ihG =>
    exact (F.setSchema.product_native_class hc G.setSchema z (F.setSchema_valid hc z h.1)
      (G.setSchema_valid hc z h.2)).trans (congrArg₂ (fun x y => x*y) (ihF h.1) (ihG h.2))

end DiamondIntegral.Section5
