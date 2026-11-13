module

public import «section 4».EulerBoundedGenerators
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The actual bounded finite-jump function quotient by p_gamma-p_0 and
o_gamma+p_0 is Z. This identifies the generated ideal with the kernel;
the quotient conclusion is not taken as a premise. The first-order Gamma
and RV/RES category bridges remain separate. -/

set_option autoImplicit false
@[expose] public noncomputable section
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ]

def boundedEulerGenerators (k : EulerKind) : Set (boundedSubring (Γ := Γ) k) :=
  {x | ∃ a : Γ, x = boundedPoint k a - boundedPoint k 0} ∪
  {x | ∃ a : Γ, x = boundedIntervalElement k a + boundedPoint k 0}

def boundedEulerIdeal (k : EulerKind) : Ideal (boundedSubring (Γ := Γ) k) :=
  Ideal.span (boundedEulerGenerators k)

abbrev BoundedFunctionQuotient (k : EulerKind) :=
  (boundedSubring (Γ := Γ) k) ⧸ boundedEulerIdeal k

theorem point_relation_mem (k : EulerKind) (a : Γ) :
    boundedPoint k a - boundedPoint k 0 ∈ boundedEulerIdeal k := by
  apply Ideal.subset_span
  exact Or.inl ⟨a, rfl⟩

theorem interval_relation_mem (k : EulerKind) (a : Γ) :
    boundedIntervalElement k a + boundedPoint k 0 ∈ boundedEulerIdeal k := by
  apply Ideal.subset_span
  exact Or.inr ⟨a, rfl⟩

theorem boundedEulerIdeal_le_kernel (k : EulerKind) :
    boundedEulerIdeal (Γ := Γ) k ≤ RingHom.ker (boundedEuler k) := by
  apply Ideal.span_le.mpr
  rintro x (⟨a, rfl⟩ | ⟨a, rfl⟩)
  · apply RingHom.mem_ker.mpr
    rw [map_sub, boundedEuler_point, boundedEuler_point, sub_self]
  · apply RingHom.mem_ker.mpr
    rw [map_add, boundedEuler_interval, boundedEuler_point]
    exact neg_add_cancel 1

def boundedQuotientMap (k : EulerKind) :
    boundedSubring (Γ := Γ) k →+* BoundedFunctionQuotient (Γ := Γ) k :=
  Ideal.Quotient.mk (boundedEulerIdeal k)

theorem boundedQuotientMap_point (k : EulerKind) (a : Γ) :
    boundedQuotientMap k (boundedPoint k a) = 1 := by
  have he := Ideal.Quotient.eq_zero_iff_mem.mpr (point_relation_mem k a)
  change boundedQuotientMap k (boundedPoint k a - boundedPoint k 0) = 0 at he
  rw [map_sub, boundedPoint_zero, map_one] at he
  exact sub_eq_zero.mp he

theorem boundedQuotientMap_interval (k : EulerKind) (a : Γ) :
    boundedQuotientMap k (boundedIntervalElement k a) = -1 := by
  have he := Ideal.Quotient.eq_zero_iff_mem.mpr (interval_relation_mem k a)
  change boundedQuotientMap k (boundedIntervalElement k a + boundedPoint k 0) = 0 at he
  rw [map_add, boundedPoint_zero, map_one] at he
  calc
    _ = (boundedQuotientMap k (boundedIntervalElement k a) + 1) - 1 := by abel
    _ = -1 := by rw [he, zero_sub]

theorem boundedQuotientMap_eq_intEuler (k : EulerKind) :
    boundedQuotientMap (Γ := Γ) k =
      (Int.castRingHom (BoundedFunctionQuotient (Γ := Γ) k)).comp (boundedEuler k) := by
  have he : (boundedQuotientMap (Γ := Γ) k).toAddMonoidHom =
      ((Int.castRingHom (BoundedFunctionQuotient (Γ := Γ) k)).comp
        (boundedEuler k)).toAddMonoidHom := by
    apply bounded_additive_ext k
    · intro a
      change boundedQuotientMap k (boundedPoint k a) =
        (Int.castRingHom (BoundedFunctionQuotient k)) (boundedEuler k (boundedPoint k a))
      rw [boundedQuotientMap_point, boundedEuler_point, map_one]
    · intro a
      change boundedQuotientMap k (boundedIntervalElement k a) =
        (Int.castRingHom (BoundedFunctionQuotient k)) (boundedEuler k (boundedIntervalElement k a))
      rw [boundedQuotientMap_interval, boundedEuler_interval, map_neg, map_one]
  exact RingHom.ext (fun x => DFunLike.congr_fun he x)

theorem boundedQuotientMap_apply (k : EulerKind) (f : boundedSubring (Γ := Γ) k) :
    boundedQuotientMap k f =
      (Int.castRingHom (BoundedFunctionQuotient (Γ := Γ) k)) (boundedEuler k f) :=
  DFunLike.congr_fun (boundedQuotientMap_eq_intEuler k) f

theorem boundedEulerIdeal_eq_kernel (k : EulerKind) :
    boundedEulerIdeal (Γ := Γ) k = RingHom.ker (boundedEuler k) := by
  apply le_antisymm (boundedEulerIdeal_le_kernel k)
  intro f hf
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change boundedQuotientMap k f = 0
  rw [boundedQuotientMap_apply, RingHom.mem_ker.mp hf, map_zero]

def quotientEuler (k : EulerKind) : BoundedFunctionQuotient (Γ := Γ) k →+* ℤ :=
  Ideal.Quotient.lift (boundedEulerIdeal k) (boundedEuler k)
    (fun _ hf => RingHom.mem_ker.mp (boundedEulerIdeal_le_kernel k hf))

theorem quotientEuler_mk (k : EulerKind) (f : boundedSubring (Γ := Γ) k) :
    quotientEuler k (boundedQuotientMap k f) = boundedEuler k f := by
  exact Ideal.Quotient.lift_mk _ _ _

def boundedEulerQuotientEquiv (k : EulerKind) :
    BoundedFunctionQuotient (Γ := Γ) k ≃+* ℤ where
  toFun := quotientEuler k
  invFun := Int.castRingHom (BoundedFunctionQuotient (Γ := Γ) k)
  left_inv q := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    change (Int.castRingHom (BoundedFunctionQuotient k))
      (quotientEuler k (boundedQuotientMap k f)) = boundedQuotientMap k f
    rw [quotientEuler_mk]
    exact (boundedQuotientMap_apply k f).symm
  right_inv n := by
    change quotientEuler k (n : BoundedFunctionQuotient k) = n
    simpa only [Int.cast_id] using map_intCast (quotientEuler (Γ := Γ) k) n
  map_add' := (quotientEuler k).map_add
  map_mul' := (quotientEuler k).map_mul

end DiamondIntegral.Section4.EulerFunction
