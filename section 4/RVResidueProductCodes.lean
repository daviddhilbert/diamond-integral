import «section 4».RVResidueCodeIndependence
import «section 4».FieldCartesianCharts
import «section 4».TupleProductBijections
import «section 4».RVMeasuredProductProperties

/-! Residue codes preserve actual RES products. The comparison uses
the original-base identity graph, not an auxiliary definable section. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResidueProductCodes
open RVResidueChartCodes RVResidueScaledCovers RVResidueCodeRelations FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def decode {n m : ℕ} {A : Set (Fin n → M)} {B : Set (Fin m → M)}
    (C : RawCode A) (D : RawCode B) (x : Fin (D.chart.arity + C.chart.arity) → ModelResidue M) :
    Fin (m + n) → CanonicalRV.RVSort M :=
  join m n (C.decode (x ∘ headIndex D.chart.arity C.chart.arity))
    (D.decode (x ∘ tailIndex D.chart.arity C.chart.arity))

theorem decode_values {n m : ℕ} {A : Set (Fin n → M)} {B : Set (Fin m → M)}
    (C : RawCode A) (D : RawCode B) (x : Fin (D.chart.arity + C.chart.arity) → ModelResidue M) :
    rvValues (decode C D x) = TupleProductBijections.map
      (fun x => rvValues (C.decode x)) (fun x => rvValues (D.decode x)) x :=
  map_join (fun t : CanonicalRV.RVSort M => t.val) m n _ _

def cover {n m : ℕ} {A : Set (Fin n → M)} {B : Set (Fin m → M)}
    (C : RawCode A) (D : RawCode B) :
    Cover (FieldCartesianCharts.product C.chart D.chart).domain (decode C D) := by
  let π : (Fin C.chart.arity ⊕ Fin D.chart.arity) → Fin (D.chart.arity + C.chart.arity) :=
    Sum.elim (headIndex D.chart.arity C.chart.arity) (tailIndex D.chart.arity C.chart.arity)
  exact (RVResidueJoinedCovers.coverJoin C.cover D.cover).reindex π

def product {n m : ℕ} {A : Set (Fin n → M)} {B : Set (Fin m → M)}
    (C : RawCode A) (D : RawCode B) : RawCode (RVRealProducts.productSet A B) where
  chart := FieldCartesianCharts.product C.chart D.chart
  decode := decode C D
  bijective := by
    have h := TupleProductBijections.bijOn
      (fun x => rvValues (C.decode x)) (fun x => rvValues (D.decode x)) C.bijective D.bijective
    change Set.BijOn (fun x : Fin (D.chart.arity + C.chart.arity) → ModelResidue M =>
      rvValues (decode C D x))
      (TupleProductBijections.domain C.chart.domain D.chart.domain) (TupleProductBijections.domain A B)
    exact h.congr (fun x _ => (decode_values C D x).symm)
  cover := cover C D

theorem value_product (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    {B : Base (M := M)} {k l : ℕ} (a : RVMeasuredCharts.RESChart B k) (b : RVMeasuredCharts.RESChart B l) :
    RVResidueIsomorphisms.value hc (RVMeasuredProductProperties.resProduct a b) =
      RVResidueIsomorphisms.value hc a * RVResidueIsomorphisms.value hc b := by
  let C := code hc a
  let D := code hc b
  have h := RVResidueCodeIndependence.code_class_value hc
    (RVMeasuredProductProperties.resProduct a b) (product C D)
  exact h.symm.trans (FieldCartesianCharts.objectClass_product C.chart D.chart)

end DiamondIntegral.Section4.RVResidueProductCodes
