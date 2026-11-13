module

public import «section 4».EulerRationalBranches
public import «section 4».EulerUnaryProjection
public import «section 4».EulerFibreIntegral

/-! Universal weighted projection for finite rational-affine branch data.
The source weight can be any actual finite-jump function. Target weights
are pulled back piece by piece, with their actual evaluations retained. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [RootableBy G ℕ]
  [DenselyOrdered G] [Nontrivial G]

theorem exists_power_law_projection {ι : Type*} (k : EulerKind) (s : Finset ι)
    (p : ι → ℤ) (q : ι → ℕ) (c : ι → G) (hq : ∀ i, q i ≠ 0)
    (T : G → G) (w : ι → EulerFunction k (Additive G))
    (hcover : ∀ i ∈ s, ∀ x : G, w i (Additive.ofMul x) ≠ 0 →
      T x ^ q i = c i * x ^ p i) :
    ∃ P : EulerFunction k (Additive G),
      IsUnaryImage k (fun x => Additive.ofMul (T (Additive.toMul x))) (∑ i ∈ s, w i) P ∧
      totalEuler k P = totalEuler k (∑ i ∈ s, w i) ∧
      ∀ g : EulerFunction k (Additive G), ∃ H : EulerFunction k (Additive G),
        (∀ x, H x = (∑ i ∈ s, w i) x * g (Additive.ofMul (T (Additive.toMul x)))) ∧
        totalEuler k H = totalEuler k (pointwiseProduct k P g) := by
  choose b hb using (fun i => power_law_branch (p i) (q i) (hq i) (c i))
  let T' : Additive G → Additive G := fun x => Additive.ofMul (T (Additive.toMul x))
  have hT : ∀ i ∈ s, ∀ x : Additive G, w i x ≠ 0 → (b i).apply x = T' x := by
    intro i hi x hx
    exact hb i (Additive.toMul x) (T (Additive.toMul x)) (hcover i hi (Additive.toMul x) hx)
  refine ⟨unaryPushforward k s b w, ?_, unary_pushforward_fubini k s b w, ?_⟩
  · intro y
    exact ⟨unaryFibre k s b w y, unaryFibre_eval_of_compatible k s b w T' hT y,
      unaryPushforward_eval k s b w y⟩
  · intro g
    exact ⟨restrictedSource k s b w g, restrictedSource_eval_of_compatible k s b w T' hT g,
      totalEuler_restrictedSource k s b w g⟩

end DiamondIntegral.Section4.EulerFunction
