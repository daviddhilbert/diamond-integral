import «section 5».RESSetProductSchemata

/-! The literal schema product realizes multiplication in the actual
native RES ring, independently of label degree and coordinate presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4 DiamondIntegral.Section4.FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

def RESSetSchema.productIso (hc : CanonicalStructure.IsCanonical (M := M))
    (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp) (z : Fin p → M)
    (hF : F.Valid hc z) (hG : G.Valid hc z) :
    RVUnderlyingIsomorphisms.Iso
      ((F.product G).chart hc z (F.product_valid hc G z hF hG)).toChart
      (RVMeasuredProductProperties.resProduct (F.chart hc z hF) (G.chart hc z hG)).toChart := by
  let S := (F.product G).chart hc z (F.product_valid hc G z hF hG)
  let T := RVMeasuredProductProperties.resProduct (F.chart hc z hF) (G.chart hc z hG)
  have he : S.domain = T.domain := by
    ext w
    rw [show S.domain = (F.product G).rowDomain z from (F.product G).chart_domain hc z _]
    change w ∈ (F.product G).rowDomain z ↔
      w ∘ headIndex b a ∈ (F.chart hc z hF).domain ∧
        w ∘ tailIndex b a ∈ (G.chart hc z hG).domain
    rw [F.chart_domain hc z hF, G.chart_domain hc z hG]
    exact F.product_row G z w
  refine RVUnderlyingIsomorphisms.ofMap S.toChart T.toChart
    (id : (Fin (b+a) → M) → (Fin (b+a) → M)) ?_ ?_
  · exact RVSharpCharts.identity_graph_definable _ _ S.domain_definable
  · change Set.BijOn id S.domain T.domain
    rw [he]
    exact Set.bijOn_id _

theorem RESSetSchema.product_native_class (hc : CanonicalStructure.IsCanonical (M := M))
    (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp) (z : Fin p → M)
    (hF : F.Valid hc z) (hG : G.Valid hc z) :
    RESDimensionFreeReduction.fromOrdinary ⟨B.real ∪ Set.range z, B.gamma⟩
      (RESOrdinaryRing.objectClass ((F.product G).chart hc z (F.product_valid hc G z hF hG))) =
    RESDimensionFreeReduction.fromOrdinary ⟨B.real ∪ Set.range z, B.gamma⟩
      (RESOrdinaryRing.objectClass (F.chart hc z hF)) *
    RESDimensionFreeReduction.fromOrdinary ⟨B.real ∪ Set.range z, B.gamma⟩
      (RESOrdinaryRing.objectClass (G.chart hc z hG)) := by
  have he := congrArg (RESDimensionFreeReduction.quotient ⟨B.real ∪ Set.range z, B.gamma⟩)
    (RESDimensionFreeRing.objectClass_iso _ _ (F.productIso hc G z hF hG))
  apply he.trans
  exact congrArg (RESDimensionFreeReduction.quotient ⟨B.real ∪ Set.range z, B.gamma⟩)
    (RESDimensionFreeRing.objectClass_product (F.chart hc z hF) (G.chart hc z hG)) |>.trans
      (map_mul _ _ _)

end DiamondIntegral.Section5
