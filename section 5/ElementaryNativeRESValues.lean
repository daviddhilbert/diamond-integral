import «section 5».ElementaryNativeRVOps
import «section 5».ElementaryNativeRVMaps
import «section 3».GammaGroundEmptyBijections

/-! Ungraded RES values of actual elementary restrictions respect native
bijections, products, empty objects, the unit and every original cut. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M N P : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
variable (hcM : CanonicalStructure.IsCanonical (M := M)) (hcN : CanonicalStructure.IsCanonical (M := N))
variable (e : M ↪ₑ[LRV] N) (c : P → M)
local notation "R" => elementaryNativeRVRestriction hcM hcN e c
local notation "Bₙ" => EmptyGammaGround.base (Set.range (e ∘ c))
local notation "Bₘ" => EmptyGammaGround.base (Set.range c)

def elementaryNativeRESValue {k : ℕ} (U : GammaGroundRESObject hcN Bₙ k) :
    RESDimensionFreeRing.Ring Bₘ :=
  nativeUngradedClass hcM (elementaryNativeRESRestriction hcM hcN e c U)

theorem elementaryNativeRESValue_bijection {k l : ℕ}
    (U : GammaGroundRESObject hcN Bₙ k) (V : GammaGroundRESObject hcN Bₙ l)
    (f : GammaGroundBijection U.obj.domain V.obj.domain) :
    elementaryNativeRESValue hcM hcN e c U = elementaryNativeRESValue hcM hcN e c V :=
  nativeUngradedClass_bijection hcM _ _ (elementaryNativeRVBijection hcM hcN e c f)

theorem elementaryNativeRESValue_empty (k : ℕ) :
    elementaryNativeRESValue hcM hcN e c (GammaGroundRESObject.empty hcN Bₙ k) = 0 := by
  have h := nativeUngradedClass_bijection hcM
    (elementaryNativeRESRestriction hcM hcN e c (GammaGroundRESObject.empty hcN Bₙ k))
    (GammaGroundRESObject.empty hcM Bₘ 0)
    (GammaGroundBijection.ofEmpty (elementaryNativeRVRestriction_empty hcM hcN e c k) rfl)
  exact h.trans (nativeUngradedClass_empty hcM Bₘ 0)

theorem elementaryNativeRESValue_product {k l : ℕ}
    (U : GammaGroundRESObject hcN Bₙ k) (V : GammaGroundRESObject hcN Bₙ l) :
    elementaryNativeRESValue hcM hcN e c (U.product V) =
      elementaryNativeRESValue hcM hcN e c U * elementaryNativeRESValue hcM hcN e c V := by
  exact (nativeUngradedClass_bijection hcM
    (elementaryNativeRESRestriction hcM hcN e c (U.product V))
    ((elementaryNativeRESRestriction hcM hcN e c U).product (elementaryNativeRESRestriction hcM hcN e c V))
    (GammaGroundBijection.ofCarrierEq (elementaryNativeRVRestriction_product hcM hcN e c U.obj.domain V.obj.domain))).trans
      (nativeUngradedClass_product hcM _ _)

theorem elementaryNativeRESValue_cut {k : ℕ} (U : GammaGroundRESObject hcN Bₙ k)
    (X : GammaGroundDefSet hcN Bₙ (rawRVSpace (M := N) U.obj.arity))
    (hX : X.carrier ⊆ U.obj.domain.carrier) :
    elementaryNativeRESValue hcM hcN e c (U.restrict X hX) +
      elementaryNativeRESValue hcM hcN e c (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)) =
        elementaryNativeRESValue hcM hcN e c U := by
  let U' := elementaryNativeRESRestriction hcM hcN e c U
  have hX' : (R X).carrier ⊆ U'.obj.domain.carrier := by
    intro x hx
    exact (elementaryNativeRVRestriction_mem hcM hcN e c U.obj.domain x).mpr
      (hX ((elementaryNativeRVRestriction_mem hcM hcN e c X x).mp hx))
  have h₁ := nativeUngradedClass_bijection hcM
    (elementaryNativeRESRestriction hcM hcN e c (U.restrict X hX)) (U'.restrict (R X) hX')
    (GammaGroundBijection.ofCarrierEq rfl)
  have h₂ := nativeUngradedClass_bijection hcM
    (elementaryNativeRESRestriction hcM hcN e c (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)))
    (U'.restrict (U'.obj.domain.sdiff (R X)) (fun _ h => h.1))
    (GammaGroundBijection.ofCarrierEq (elementaryNativeRVRestriction_sdiff hcM hcN e c U.obj.domain X))
  exact (congrArg₂ (· + ·) h₁ h₂).trans (nativeUngradedClass_cut hcM U' (R X) hX')

theorem elementaryNativeRESValue_unit :
    elementaryNativeRESValue hcM hcN e c (GammaGroundRESObject.unit hcN Bₙ) = 1 := by
  apply (nativeUngradedClass_bijection hcM
    (elementaryNativeRESRestriction hcM hcN e c (GammaGroundRESObject.unit hcN Bₙ))
    (GammaGroundRESObject.unit hcM Bₘ) ?_).trans (nativeUngradedClass_unit hcM Bₘ)
  apply GammaGroundBijection.ofCarrierEq
  ext x
  change x ∈ (R (GammaGroundRESObject.unit hcN Bₙ).obj.domain).carrier ↔
    x ∈ (GammaGroundRESObject.unit hcM Bₘ).obj.domain.carrier
  rw [elementaryNativeRVRestriction_mem]
  rfl

end DiamondIntegral.Section5
