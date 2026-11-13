module

public import «section 4».EulerUnaryPushforward

/-! Uniqueness and linearity of actual unary Euler fibre integration.
The predicate specifies the actual weighted fibres; no formal pushforward
or Fubini axiom is used. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ Δ : Type*}
  [LinearOrder Γ] [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]
  [LinearOrder Δ] [DenselyOrdered Δ] [NoMinOrder Δ] [NoMaxOrder Δ] [AddCommGroup Δ]

def IsUnaryImage (k : EulerKind) (T : Γ → Δ)
    (f : EulerFunction k Γ) (P : EulerFunction k Δ) : Prop :=
  ∀ y, ∃ F : EulerFunction k Γ,
    (∀ x, F x = if T x = y then f x else 0) ∧ P y = totalEuler k F

omit [DenselyOrdered Δ] [NoMinOrder Δ] [NoMaxOrder Δ] [AddCommGroup Δ] in
theorem IsUnaryImage.unique {k : EulerKind} {T : Γ → Δ}
    {f : EulerFunction k Γ} {P Q : EulerFunction k Δ}
    (hP : IsUnaryImage k T f P) (hQ : IsUnaryImage k T f Q) : P = Q := by
  apply eval_injective k
  funext y
  obtain ⟨F, hF, hPF⟩ := hP y
  obtain ⟨G, hG, hQG⟩ := hQ y
  have he : F = G := eval_injective k (funext (fun x => (hF x).trans (hG x).symm))
  exact hPF.trans ((congrArg (totalEuler k) he).trans hQG.symm)

theorem isUnaryImage_zero (k : EulerKind) (T : Γ → Δ) :
    IsUnaryImage k T (0 : EulerFunction k Γ) (0 : EulerFunction k Δ) := by
  intro y
  exact ⟨0, (fun x => by simp only [eval_zero, ite_self]), by simp only [eval_zero, map_zero]⟩

theorem IsUnaryImage.add {k : EulerKind} {T : Γ → Δ}
    {f g : EulerFunction k Γ} {P Q : EulerFunction k Δ}
    (hP : IsUnaryImage k T f P) (hQ : IsUnaryImage k T g Q) :
    IsUnaryImage k T (f + g) (P + Q) := by
  intro y
  obtain ⟨F, hF, hPF⟩ := hP y
  obtain ⟨G, hG, hQG⟩ := hQ y
  refine ⟨F + G, ?_, ?_⟩
  · intro x
    rw [eval_add, hF, hG, eval_add]
    by_cases h : T x = y <;> simp only [h, ite_true, ite_false, add_zero]
  · rw [eval_add, map_add, hPF, hQG]

theorem IsUnaryImage.zsmul {k : EulerKind} {T : Γ → Δ}
    {f : EulerFunction k Γ} {P : EulerFunction k Δ}
    (hP : IsUnaryImage k T f P) (n : ℤ) : IsUnaryImage k T (n • f) (n • P) := by
  intro y
  obtain ⟨F, hF, hPF⟩ := hP y
  refine ⟨n • F, ?_, ?_⟩
  · intro x
    rw [eval_zsmul, hF, eval_zsmul]
    by_cases h : T x = y <;> simp only [h, ite_true, ite_false, smul_zero]
  · rw [eval_zsmul, map_zsmul, hPF]

theorem UnaryBranch.isUnaryImage [IsOrderedAddMonoid Γ] (k : EulerKind)
    (b : UnaryBranch Γ Δ) (f : EulerFunction k Γ) : IsUnaryImage k b.apply f (b.push k f) := by
  intro y
  exact ⟨b.fibre k f y, b.fibre_eval k f y, (b.fibreEuler k f y).symm⟩

theorem isUnaryImage_id [IsOrderedAddMonoid Γ] (k : EulerKind) (f : EulerFunction k Γ) :
    IsUnaryImage k id f f := by
  have h := (UnaryBranch.increasing (OrderIso.refl Γ)).isUnaryImage k f
  have he : (UnaryBranch.increasing (OrderIso.refl Γ)).push k f = f := by
    apply eval_injective k
    funext x
    change orderPush k (OrderIso.refl Γ) f x = f x
    rw [orderPush_eval]
    rfl
  rw [he] at h
  exact h

theorem isUnaryImage_const [IsOrderedAddMonoid Γ] (k : EulerKind) (c : Δ)
    (f : EulerFunction k Γ) : IsUnaryImage k (fun _ => c) f (totalEuler k f • point k c) :=
  (UnaryBranch.constant c).isUnaryImage k f

end DiamondIntegral.Section4.EulerFunction
