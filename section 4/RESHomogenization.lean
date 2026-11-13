import «section 4».RVUnderlyingProducts
import «section 4».RESPointTuples

/-! An actual underlying bijection between RES objects of different
degrees becomes a same-degree ordinary RES isomorphism after multiplying
by concrete point objects. This proves the point-factor identity needed
for the dimension-free presentation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESHomogenization
open RVMeasuredCharts RVMeasuredProductProperties
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def castRES {B : Base (M := M)} {k l : ℕ} (h : k = l) (a : RESChart B k) : RESChart B l := h ▸ a

theorem ordinary_cast {B : Base (M := M)} {k l : ℕ} (h : k = l) (a : RESChart B k) :
    RESOrdinaryRing.objectClass (castRES h a) = RESOrdinaryRing.objectClass a := by
  cases h
  rfl

def castTarget {B : Base (M := M)} {k l n : ℕ} {a : RESChart B k} {b : RESChart B l}
    (h : l = n) (F : RVUnderlyingIsomorphisms.Iso a.toChart b.toChart) :
    RVUnderlyingIsomorphisms.Iso a.toChart (castRES h b).toChart := by
  cases h
  exact F

def homogenizingIso {B : Base (M := M)} {k l : ℕ} (a : RESChart B k) (b : RESChart B l)
    (F : RVUnderlyingIsomorphisms.Iso a.toChart b.toChart) :
    RVForgetScissors.UnderlyingIso (resProduct a (RESPointTuples.res B l)).toChart
      (castRES (Nat.add_comm k l) (resProduct b (RESPointTuples.res B k))).toChart :=
  RVUnderlyingIsomorphisms.toFixed (castTarget (Nat.add_comm k l)
    (RVUnderlyingProducts.productIso F (RESPointTuples.underlyingIso B l k)))

theorem ordinary_homogenization {B : Base (M := M)} {k l : ℕ} (a : RESChart B k) (b : RESChart B l)
    (F : RVUnderlyingIsomorphisms.Iso a.toChart b.toChart) :
    RESOrdinaryRing.objectClass a * RESOrdinaryRing.objectClass (RESPointTuples.res B 1) ^ l =
      RESOrdinaryRing.objectClass b * RESOrdinaryRing.objectClass (RESPointTuples.res B 1) ^ k := by
  have he := RESOrdinaryRing.objectClass_iso (homogenizingIso a b F)
  rw [ordinary_cast, RESOrdinaryRing.objectClass_product, RESOrdinaryRing.objectClass_product,
    RESPointTuples.ordinary_power B l, RESPointTuples.ordinary_power B k] at he
  exact he

end DiamondIntegral.Section4.RESHomogenization
