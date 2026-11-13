import «section 4».GammaOrdinaryRing
import «section 4».RVOrdinaryRing
import «section 4».RVSharpProducts
import «section 4».RVSharpScissors

/-! Actual sharp objects for ordinary Gamma charts preserve the unit,
products, empty sets and ordinary scissors in the ordinary RV ring.
Changes of Gamma volume forms require only an underlying RV identity. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinarySharpObjects
open GammaOrdinaryCharts GammaDefinableMaps GammaRVChartPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def sameSupportIso {B : Base (M := M)} {n : ℕ} (a b : GammaWeightedCharts.Chart B n) (hs : a.support = b.support) :
    RVForgetScissors.UnderlyingIso (RVSharpCharts.sharpChart a) (RVSharpCharts.sharpChart b) := by
  apply RVForgetScissors.ofMap _ _ (id : (Fin n → M) → (Fin n → M))
  · change DefinableOverBase B (fun _ : Fin (n + n) => .rv) (RVMeasuredCharts.graphOn (sharp a.support) id)
    exact RVSharpCharts.identity_graph_definable B (sharp a.support) (sharp_definable a.support a.support_definable)
  · change Set.BijOn id (sharp a.support) (sharp b.support)
    rw [hs]
    exact Set.bijOn_id _

theorem sharp_unit (B : Base (M := M)) : RVOrdinaryRing.objectClass (sharpChart (GammaOrdinaryCharts.unit B)) = 1 :=
  (RVOrdinaryRing.objectClass_iso (RVForgetScissors.ofMeasured (RVSharpProducts.sharpUnitIso B))).trans (RVOrdinaryRing.objectClass_unit B)

theorem sharp_product {B : Base (M := M)} {n m : ℕ} (a : Chart B m) (b : Chart B n) :
    RVOrdinaryRing.objectClass (sharpChart (product a b)) = RVOrdinaryRing.objectClass (sharpChart a) * RVOrdinaryRing.objectClass (sharpChart b) := by
  have he := RVOrdinaryRing.objectClass_iso (sameSupportIso (toWeighted (product a b))
    (GammaChartOperations.product (toWeighted a) (toWeighted b)) rfl)
  exact he.trans ((RVOrdinaryRing.objectClass_iso (RVForgetScissors.ofMeasured
    (RVSharpProducts.sharpProductIso (toWeighted a) (toWeighted b)))).trans (RVOrdinaryRing.objectClass_product _ _))

theorem sharp_empty {B : Base (M := M)} {n : ℕ} (a : Chart B n) (ha : a.support = ∅) : RVOrdinaryRing.objectClass (sharpChart a) = 0 := by
  apply RVOrdinaryRing.objectClass_empty
  change sharp a.support = ∅
  rw [ha]
  ext z
  exact ⟨fun h => h.2.elim, fun h => h.elim⟩

theorem sharp_scissor {B : Base (M := M)} {n : ℕ} (a b c d : Chart B n) (h : GammaOrdinaryRing.Scissor a b c d) :
    RVOrdinaryRing.objectClass (sharpChart c) + RVOrdinaryRing.objectClass (sharpChart d) =
      RVOrdinaryRing.objectClass (sharpChart a) + RVOrdinaryRing.objectClass (sharpChart b) := by
  let hU := GammaQuantifierLogic.union_definable_base B _ _ a.support_definable b.support_definable
  let hN := GammaRelationLogic.inter_definable_base B _ _ a.support_definable b.support_definable
  let h1 : MapDefinable B (fun _ : Fin n → Values.Gamma (M := M) => 1) := constant_definable B 1 (GammaGroupNames.one_definable_base B)
  let u := GammaChartOperations.ofTotal B n (a.support ∪ b.support) hU (fun _ => 1) h1
  let i := GammaChartOperations.ofTotal B n (a.support ∩ b.support) hN (fun _ => 1) h1
  have hc := RVOrdinaryRing.objectClass_iso (sameSupportIso (toWeighted c) u h.1)
  have hd := RVOrdinaryRing.objectClass_iso (sameSupportIso (toWeighted d) i h.2)
  change RVOrdinaryRing.objectClass (RVSharpCharts.sharpChart (toWeighted c)) +
    RVOrdinaryRing.objectClass (RVSharpCharts.sharpChart (toWeighted d)) =
    RVOrdinaryRing.objectClass (RVSharpCharts.sharpChart (toWeighted a)) +
      RVOrdinaryRing.objectClass (RVSharpCharts.sharpChart (toWeighted b))
  rw [hc, hd]
  exact RVOrdinaryRing.objectClass_scissor _ _ _ _ (RVForgetScissors.measured_scissor _ _ _ _
    (RVSharpScissors.sharp_scissor B n a.support b.support a.support_definable b.support_definable hU hN (fun _ => 1) h1))

end DiamondIntegral.Section4.GammaOrdinarySharpObjects
