module

public import «section 4».EulerFunctions

/-! Canonical additive decomposition of actual finite-jump functions.
It supplies the generator induction used in the convolution comparison. -/

@[expose] public noncomputable section
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]

def evaluation (k : EulerKind) (x : Γ) : EulerFunction k Γ →+ ℤ where
  toFun f := f x
  map_zero' := eval_zero k x
  map_add' f g := eval_add k f g x

theorem eval_zsmul (k : EulerKind) (n : ℤ) (f : EulerFunction k Γ) (x : Γ) :
    (n • f) x = n • (f x) := map_zsmul (evaluation k x) n f

theorem eval_finsuppSum {ι : Type*} (k : EulerKind) (p : ι →₀ ℤ)
    (f : ι → ℤ → EulerFunction k Γ) (x : Γ) :
    (p.sum f) x = p.sum (fun a n => f a n x) :=
  map_sum (evaluation k x) (fun a => f a (p a)) p.support

def coefficientEquiv (k : EulerKind) : StepCoefficients Γ ≃+ EulerFunction k Γ :=
  (normalCoordinates k).trans (eulerCoordinatesRingEquiv k).symm.toAddEquiv

def ofCoefficients (k : EulerKind) (v : StepCoefficients Γ) : EulerFunction k Γ :=
  coefficientEquiv k v

theorem ofCoefficients_eval (k : EulerKind) (v : StepCoefficients Γ) (x : Γ) :
    ofCoefficients k v x = stepEval v x := by
  change ofModel k (normalCoordinates k v) x = _
  rw [ofModel_eval, modelFunctionEquiv_eval, AddEquiv.symm_apply_apply]

def linearCombination (k : EulerKind) (v : StepCoefficients Γ) : EulerFunction k Γ :=
  v.1 • line k + v.2.1.sum (fun a n => n • point k a) +
    v.2.2.sum (fun a n => n • ray k a)

theorem linearCombination_eval (k : EulerKind) (v : StepCoefficients Γ) (x : Γ) :
    linearCombination k v x = stepEval v x := by
  simp only [linearCombination, eval_add, eval_finsuppSum, eval_zsmul,
    line_eval, point_eval, ray_eval]
  simp only [zsmul_eq_mul, mul_ite, mul_one, mul_zero]
  simp only [Int.cast_id]
  rw [Finsupp.sum_ite_self_eq]
  rfl

theorem ofCoefficients_eq_linearCombination (k : EulerKind) (v : StepCoefficients Γ) :
    ofCoefficients k v = linearCombination k v := by
  apply eval_injective k
  funext x
  exact (ofCoefficients_eval k v x).trans (linearCombination_eval k v x).symm

theorem generator_expansion (k : EulerKind) (f : EulerFunction k Γ) :
    ∃ v : StepCoefficients Γ, f = linearCombination k v := by
  obtain ⟨v, hv⟩ := (coefficientEquiv k).surjective f
  exact ⟨v, hv.symm.trans (ofCoefficients_eq_linearCombination k v)⟩

theorem additive_ext {A : Type*} [AddCommGroup A] (k : EulerKind)
    (f g : EulerFunction k Γ →+ A)
    (hr : f (line k) = g (line k))
    (hp : ∀ a, f (point k a) = g (point k a))
    (hq : ∀ a, f (ray k a) = g (ray k a)) : f = g := by
  apply AddMonoidHom.ext
  intro h
  obtain ⟨v, rfl⟩ := generator_expansion k h
  simp only [linearCombination, Finsupp.sum, map_add, map_sum, map_zsmul, hr, hp, hq]

end DiamondIntegral.Section4.EulerFunction
