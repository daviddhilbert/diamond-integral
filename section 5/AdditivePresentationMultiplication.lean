import Section4.PositiveAdditiveRepresentatives
import Section4.Imported.GrothendieckRing

/-! Multiplication on a positive additive presentation is constructed
from additive product invariants. An additive total-family invariant need
not preserve products, and still extends to the resulting group completion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
universe u
variable {Obj : Type u} {P : Presentation Obj}

structure PositiveProductData (P : Presentation Obj) where
  sum : Obj → Obj → Obj
  sum_class : ∀ a b, of P (sum a b) = of P a + of P b
  mul : Obj → Obj → Obj
  one : Obj
  productInvariant : ∀ a, Invariant P (A := KPlus P)
  product_value : ∀ a b, (productInvariant a).toFun b = of P (mul a b)
  comm : ∀ a b, of P (mul a b) = of P (mul b a)
  assoc : ∀ a b c, of P (mul (mul a b) c) = of P (mul a (mul b c))
  one_left : ∀ a, of P (mul one a) = of P a

def PositiveProductData.leftMultiply (D : PositiveProductData P) (a : Obj) : KPlus P →+ KPlus P :=
  lift P (D.productInvariant a)

theorem PositiveProductData.leftMultiply_of (D : PositiveProductData P) (a b : Obj) :
    D.leftMultiply a (of P b) = of P (D.mul a b) :=
  (lift_of P (D.productInvariant a) b).trans (D.product_value a b)

theorem PositiveProductData.leftMultiply_comm (D : PositiveProductData P) (a b : Obj) :
    D.leftMultiply a (of P b) = D.leftMultiply b (of P a) := by
  rw [D.leftMultiply_of,D.leftMultiply_of]
  exact D.comm a b

def PositiveProductData.rightInvariant (D : PositiveProductData P) :
    Invariant P (A := KPlus P →+ KPlus P) where
  toFun := D.leftMultiply
  iso := by
    intro a c h
    apply hom_ext P
    intro b
    calc
      D.leftMultiply a (of P b) = D.leftMultiply b (of P a) := D.leftMultiply_comm a b
      _ = D.leftMultiply b (of P c) := congrArg (D.leftMultiply b) (of_iso P h)
      _ = D.leftMultiply c (of P b) := D.leftMultiply_comm c b |>.symm
  empty := by
    apply hom_ext P
    intro b
    rw [D.leftMultiply_comm,of_empty,map_zero]
    rfl
  scissor := by
    intro a b c d h
    apply hom_ext P
    intro e
    change D.leftMultiply a (of P e) + D.leftMultiply b (of P e) =
      D.leftMultiply c (of P e) + D.leftMultiply d (of P e)
    rw [D.leftMultiply_comm a e,D.leftMultiply_comm b e,
      D.leftMultiply_comm c e,D.leftMultiply_comm d e,← map_add,← map_add]
    exact congrArg (D.leftMultiply e) (of_scissor P h)

def PositiveProductData.bilinear (D : PositiveProductData P) : KPlus P →+ KPlus P →+ KPlus P :=
  lift P D.rightInvariant

theorem PositiveProductData.bilinear_of (D : PositiveProductData P) (a : Obj) :
    D.bilinear (of P a) = D.leftMultiply a := lift_of P D.rightInvariant a

theorem PositiveProductData.bilinear_of_of (D : PositiveProductData P) (a b : Obj) :
    D.bilinear (of P a) (of P b) = of P (D.mul a b) := by
  rw [D.bilinear_of,D.leftMultiply_of]

theorem PositiveProductData.bilinear_assoc (D : PositiveProductData P) (x y z : KPlus P) :
    D.bilinear (D.bilinear x y) z = D.bilinear x (D.bilinear y z) := by
  obtain ⟨a,rfl⟩ := of_surjective P D.sum D.sum_class x
  obtain ⟨b,rfl⟩ := of_surjective P D.sum D.sum_class y
  obtain ⟨c,rfl⟩ := of_surjective P D.sum D.sum_class z
  simp only [D.bilinear_of_of]
  exact D.assoc a b c

theorem PositiveProductData.bilinear_comm (D : PositiveProductData P) (x y : KPlus P) :
    D.bilinear x y = D.bilinear y x := by
  obtain ⟨a,rfl⟩ := of_surjective P D.sum D.sum_class x
  obtain ⟨b,rfl⟩ := of_surjective P D.sum D.sum_class y
  rw [D.bilinear_of_of,D.bilinear_of_of]
  exact D.comm a b

theorem PositiveProductData.bilinear_one_left (D : PositiveProductData P) (x : KPlus P) :
    D.bilinear (of P D.one) x = x := by
  obtain ⟨a,rfl⟩ := of_surjective P D.sum D.sum_class x
  rw [D.bilinear_of_of]
  exact D.one_left a

@[instance_reducible]
def positiveProductCommSemiring (D : PositiveProductData P) : CommSemiring (KPlus P) where
  toAddCommMonoid := inferInstance
  mul := fun x y => D.bilinear x y
  one := of P D.one
  mul_assoc := D.bilinear_assoc
  mul_comm := D.bilinear_comm
  one_mul := D.bilinear_one_left
  mul_one x := (D.bilinear_comm x (of P D.one)).trans (D.bilinear_one_left x)
  left_distrib x y z := (D.bilinear x).map_add y z
  right_distrib x y z := by
    change D.bilinear (x+y) z = D.bilinear x z + D.bilinear y z
    exact congrArg (fun f : KPlus P →+ KPlus P => f z) (D.bilinear.map_add x y)
  mul_zero x := (D.bilinear x).map_zero
  zero_mul x := by
    change D.bilinear 0 x = 0
    exact congrArg (fun f : KPlus P →+ KPlus P => f x) D.bilinear.map_zero
  natCast := fun n => n • of P D.one
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    change (n+1) • of P D.one = n • of P D.one + of P D.one
    exact succ_nsmul (of P D.one) n

def positiveProductCompletionClass (D : PositiveProductData P) (a : Obj) :
    letI := positiveProductCommSemiring D
    Algebra.GrothendieckAddGroup (KPlus P) := Algebra.GrothendieckAddGroup.of (of P a)

def positiveProductAdditiveLift (D : PositiveProductData P) {A : Type*} [AddCommGroup A]
    (f : Invariant P (A := A)) :
    letI := positiveProductCommSemiring D
    Algebra.GrothendieckAddGroup (KPlus P) →+ A :=
  Algebra.GrothendieckAddGroup.lift (lift P f)

theorem positiveProductAdditiveLift_class (D : PositiveProductData P) {A : Type*} [AddCommGroup A]
    (f : Invariant P (A := A)) (a : Obj) :
    positiveProductAdditiveLift D f (positiveProductCompletionClass D a) = f.toFun a :=
  (Algebra.GrothendieckAddGroup.lift_apply_of (lift P f) (of P a)).trans (lift_of P f a)

end DiamondIntegral.Section5
