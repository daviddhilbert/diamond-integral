import «section 4».GammaRVChartPresentation

/-! Class relations and universal property of the Gamma chart ring whose
isomorphisms retain actual original-base RV-contraction lifts. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaRVChartPresentation
open GammaWeightedCharts GammaChartOperations GammaChartPresentation
open GammaOrderLogic GammaDefinableMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def objectClass {B : Base (M := M)} {n : ℕ} (a : Chart B n) : ChartRing B :=
  Ideal.Quotient.mk (relationIdeal B) (symbol a)

theorem relation_zero (B : Base (M := M)) (r : FreeCommRing (Generator B)) (hr : Relation B r) :
    Ideal.Quotient.mk (relationIdeal B) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)

theorem class_unit (B : Base (M := M)) : objectClass (GammaChartOperations.unit B) = 1 := by
  have h := relation_zero B _ Relation.unit
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

theorem class_product {B : Base (M := M)} {n m : ℕ} (a : Chart B m) (b : Chart B n) :
    objectClass (GammaChartOperations.product a b) = objectClass a * objectClass b := by
  have h := relation_zero B _ (Relation.product a b)
  rw [map_sub, map_mul] at h
  exact sub_eq_zero.mp h

theorem class_iso {B : Base (M := M)} {n : ℕ} {a b : Chart B n} (F : RVVolumeIso a b) :
    objectClass a = objectClass b := by
  have h := relation_zero B _ (Relation.iso a b F)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem class_empty (B : Base (M := M)) (n : ℕ)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    objectClass (ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) μ hμ) = 0 :=
  relation_zero B _ (Relation.empty n μ hμ)

theorem class_scissor (B : Base (M := M)) (n : ℕ)
    (I J : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hJ : GammaDefinable B J)
    (hU : GammaDefinable B (I ∪ J)) (hN : GammaDefinable B (I ∩ J))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    objectClass (ofTotal B n (I ∪ J) hU μ hμ) + objectClass (ofTotal B n (I ∩ J) hN μ hμ) =
      objectClass (ofTotal B n I hI μ hμ) + objectClass (ofTotal B n J hJ μ hμ) := by
  have h := relation_zero B _ (Relation.scissor n I J hI hJ hU hN μ hμ)
  rw [map_sub, map_sub, map_add, sub_sub] at h
  exact sub_eq_zero.mp h

structure Invariant (B : Base (M := M)) (R : Type*) [CommRing R] where
  value : ∀ n, Chart B n → R
  unit : value 0 (GammaChartOperations.unit B) = 1
  product : ∀ n m (a : Chart B m) (b : Chart B n), value (n + m) (GammaChartOperations.product a b) = value m a * value n b
  iso : ∀ n (a b : Chart B n), RVVolumeIso a b → value n a = value n b
  empty : ∀ n μ hμ, value n (ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) μ hμ) = 0
  scissor : ∀ n I J hI hJ hU hN μ hμ,
    value n (ofTotal B n (I ∪ J) hU μ hμ) + value n (ofTotal B n (I ∩ J) hN μ hμ) =
      value n (ofTotal B n I hI μ hμ) + value n (ofTotal B n J hJ μ hμ)

def freeMap (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) :
    FreeCommRing (Generator B) →+* R := FreeCommRing.lift (fun a => f.value a.1 a.2)

theorem freeMap_symbol (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    {n : ℕ} (a : Chart B n) : freeMap B f (symbol a) = f.value n a := FreeCommRing.lift_of _ _

theorem invariant_relation_zero (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    (r : FreeCommRing (Generator B)) (hr : Relation B r) : freeMap B f r = 0 := by
  cases hr with
  | unit => rw [map_sub, map_one, freeMap_symbol, f.unit, sub_self]
  | product a b => rw [map_sub, map_mul, freeMap_symbol, freeMap_symbol, freeMap_symbol, f.product, sub_self]
  | iso a b F => rw [map_sub, freeMap_symbol, freeMap_symbol, f.iso _ a b F, sub_self]
  | empty n μ hμ => rw [freeMap_symbol, f.empty n μ hμ]
  | scissor n I J hI hJ hU hN μ hμ =>
    simp only [map_sub, map_add, freeMap_symbol, sub_sub]
    exact sub_eq_zero.mpr (f.scissor n I J hI hJ hU hN μ hμ)

theorem invariant_ideal_zero (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) :
    relationIdeal B ≤ RingHom.ker (freeMap B f) := by
  apply Ideal.span_le.mpr
  intro r hr
  exact invariant_relation_zero B f r hr

def lift (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) : ChartRing B →+* R :=
  Ideal.Quotient.lift (relationIdeal B) (freeMap B f) (fun _ hr => invariant_ideal_zero B f hr)

theorem lift_class (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    {n : ℕ} (a : Chart B n) : lift B f (objectClass a) = f.value n a := freeMap_symbol B f a

theorem hom_ext (B : Base (M := M)) {R : Type*} [CommRing R]
    (f g : ChartRing B →+* R) (h : ∀ n (a : Chart B n), f (objectClass a) = g (objectClass a)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro a
  exact h a.1 a.2

end DiamondIntegral.Section4.GammaRVChartPresentation
