module

public import «section 4».EulerBoundedSupport

/-! The two Euler theories agree on actual bounded functions. The common
function is retained while changing its generator-ring structure. -/

@[expose] public noncomputable section
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]

def changeKind (k l : EulerKind) : EulerFunction k Γ ≃+ EulerFunction l Γ :=
  (coefficientEquiv k).symm.trans (coefficientEquiv l)

theorem changeKind_eval (k l : EulerKind) (f : EulerFunction k Γ) (x : Γ) :
    changeKind k l f x = f x := by
  change ofCoefficients l ((coefficientEquiv k).symm f) x = f x
  rw [ofCoefficients_eval]
  exact coefficients_eval k f x

theorem changeKind_coefficients (k l : EulerKind) (f : EulerFunction k Γ) :
    (coefficientEquiv l).symm (changeKind k l f) = (coefficientEquiv k).symm f := by
  change (coefficientEquiv l).symm (coefficientEquiv l ((coefficientEquiv k).symm f)) = _
  exact (coefficientEquiv l).symm_apply_apply _

theorem changeKind_self (k : EulerKind) (f : EulerFunction k Γ) : changeKind k k f = f := by
  apply eval_injective k
  funext x
  exact changeKind_eval k k f x

theorem changeKind_trans (k l m : EulerKind) (f : EulerFunction k Γ) :
    changeKind l m (changeKind k l f) = changeKind k m f := by
  apply eval_injective m
  funext x
  change changeKind l m (changeKind k l f) x = changeKind k m f x
  rw [changeKind_eval, changeKind_eval, changeKind_eval]

theorem totalEuler_ofCoefficients (k : EulerKind) (v : StepCoefficients Γ) :
    totalEuler k (ofCoefficients k v) =
      k.lineValue * v.1 + coefficientSum v.2.1 + k.rayValue * coefficientSum v.2.2 := by
  change ((eulerCoordinatesRingEquiv k)
    ((eulerCoordinatesRingEquiv k).symm (normalCoordinates k v))).1 = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem totalEuler_coefficients (k : EulerKind) (f : EulerFunction k Γ) :
    totalEuler k f = k.lineValue * ((coefficientEquiv k).symm f).1 +
      coefficientSum ((coefficientEquiv k).symm f).2.1 +
      k.rayValue * coefficientSum ((coefficientEquiv k).symm f).2.2 := by
  simpa only [ofCoefficients, AddEquiv.apply_symm_apply] using
    totalEuler_ofCoefficients k ((coefficientEquiv k).symm f)

theorem IsDoublyBounded.changeKind {k : EulerKind} {f : EulerFunction k Γ}
    (hf : IsDoublyBounded f) (l : EulerKind) : IsDoublyBounded (changeKind k l f) := by
  obtain ⟨a, b, h⟩ := hf
  exact ⟨a, b, fun x hx => h x (by simpa only [changeKind_eval] using hx)⟩

theorem totalEuler_of_bounded (k : EulerKind) (f : EulerFunction k Γ) (hf : IsDoublyBounded f) :
    totalEuler k f = coefficientSum ((coefficientEquiv k).symm f).2.1 := by
  obtain ⟨hc, hq⟩ := (isDoublyBounded_iff_coefficients k f).mp hf
  rw [totalEuler_coefficients, hc, hq, mul_zero, zero_add, mul_zero, add_zero]

theorem totalEuler_changeKind (k l : EulerKind) (f : EulerFunction k Γ) (hf : IsDoublyBounded f) :
    totalEuler l (changeKind k l f) = totalEuler k f := by
  rw [totalEuler_of_bounded l _ (hf.changeKind l), totalEuler_of_bounded k f hf,
    changeKind_coefficients]

theorem IsDoublyBounded.pointwise_left {k : EulerKind} {f : EulerFunction k Γ}
    (hf : IsDoublyBounded f) (g : EulerFunction k Γ) : IsDoublyBounded (pointwiseProduct k f g) := by
  obtain ⟨a, b, h⟩ := hf
  refine ⟨a, b, ?_⟩
  intro x hx
  apply h x
  intro hz
  exact hx (by rw [pointwiseProduct_eval, hz, zero_mul])

theorem changeKind_pointwiseProduct (k l : EulerKind) (f g : EulerFunction k Γ) :
    changeKind k l (pointwiseProduct k f g) =
      pointwiseProduct l (changeKind k l f) (changeKind k l g) := by
  apply eval_injective l
  funext x
  change changeKind k l (pointwiseProduct k f g) x =
    pointwiseProduct l (changeKind k l f) (changeKind k l g) x
  rw [changeKind_eval, pointwiseProduct_eval, pointwiseProduct_eval,
    changeKind_eval, changeKind_eval]

variable [IsOrderedAddMonoid Γ]

theorem changeKind_reflectAt (k l : EulerKind) (t : Γ) (f : EulerFunction k Γ) :
    changeKind k l (reflectAt k t f) = reflectAt l t (changeKind k l f) := by
  apply eval_injective l
  funext x
  change changeKind k l (reflectAt k t f) x = reflectAt l t (changeKind k l f) x
  rw [changeKind_eval, reflectAt_eval, reflectAt_eval, changeKind_eval]

theorem changeKind_mul_of_bounded (k l : EulerKind) (f g : EulerFunction k Γ)
    (hf : IsDoublyBounded f) :
    changeKind k l (f * g) = changeKind k l f * changeKind k l g := by
  apply eval_injective l
  funext t
  have hi := hf.pointwise_left (reflectAt k t g)
  have he := totalEuler_changeKind k l (pointwiseProduct k f (reflectAt k t g)) hi
  have hb : changeKind k l (pointwiseProduct k f (reflectAt k t g)) =
      pointwiseProduct l (changeKind k l f) (reflectAt l t (changeKind k l g)) := by
    rw [changeKind_pointwiseProduct, changeKind_reflectAt]
  change changeKind k l (f * g) t = (changeKind k l f * changeKind k l g) t
  calc
    _ = (f * g) t := changeKind_eval k l (f * g) t
    _ = convolutionValue k f g t := (convolutionValue_eq_product k f g t).symm
    _ = convolutionValue l (changeKind k l f) (changeKind k l g) t := by
      unfold convolutionValue
      rw [← hb]
      exact he.symm
    _ = _ := convolutionValue_eq_product l _ _ t

def boundedKindEquiv (k l : EulerKind) :
    boundedSubring (Γ := Γ) k ≃+* boundedSubring (Γ := Γ) l where
  toFun f := ⟨changeKind k l f.val, f.property.changeKind l⟩
  invFun g := ⟨changeKind l k g.val, g.property.changeKind k⟩
  left_inv f := by
    apply Subtype.ext
    change changeKind l k (changeKind k l f.val) = f.val
    rw [changeKind_trans, changeKind_self]
  right_inv g := by
    apply Subtype.ext
    change changeKind k l (changeKind l k g.val) = g.val
    rw [changeKind_trans, changeKind_self]
  map_add' f g := Subtype.ext ((changeKind k l).map_add f.val g.val)
  map_mul' f g := Subtype.ext (changeKind_mul_of_bounded k l f.val g.val f.property)

def boundedEuler (k : EulerKind) : boundedSubring (Γ := Γ) k →+* ℤ :=
  (totalEuler k).comp (boundedSubring k).subtype

end DiamondIntegral.Section4.EulerFunction
