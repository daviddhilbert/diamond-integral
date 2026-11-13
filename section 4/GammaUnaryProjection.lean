import «section 4».GammaUnaryPushforwardMap
import «section 4».GammaPowerLawCells
import «section 4».EulerRationalProjection

/-! Weighted projection for any actual finite-jump source weight under a
definable unary Gamma map. Only the map's finite power-law cover comes from
the authorized [18] linearity input; the fibre and projection identities
are proved here. Source and target weights may carry extra endpoints. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaUnaryProjection
open GammaOrderLogic GammaDefinableEuler GammaEulerSets GammaBaseExtension GammaPowerLawCells
open GammaUnaryPushforwardMap EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem exists_unary_projection (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (B : Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (T : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | T (z 0) = z 1})
    (f : EulerFunction k (PaperGamma (M := M))) :
    ∃ P : EulerFunction k (PaperGamma (M := M)), IsUnaryImage k (paperMap T) f P ∧
      totalEuler k P = totalEuler k f ∧
      ∀ g : EulerFunction k (PaperGamma (M := M)), ∃ H : EulerFunction k (PaperGamma (M := M)),
        (∀ x, H x = f x * g (paperMap T x)) ∧
        totalEuler k H = totalEuler k (pointwiseProduct k P g) := by
  have hGraph : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) |
      z 0 ∈ (Set.univ : Set (Values.Gamma (M := M))) ∧ T (z 0) = z 1} := by
    simpa only [Set.mem_univ, true_and] using hT
  have hTc := to_common_real_syntax B _ hGraph
  obtain ⟨m, p, q, c, hq, hcover⟩ := linear h00 (commonRealNames B)
    (GammaUnaryBijections.nontrivial_commonBase B hΓ) Set.univ T hTc
  let C := fun i => lawCell Set.univ T (p i) (q i) (c i)
  let B' := withGamma B (Set.range c)
  have hC : ∀ i, GammaDefinableOverBase B' (C i) :=
    lawCells_definable_extend B Set.univ T hGraph p q c
  have hPi (i : Fin m) : GammaDefinableOverBase B' (firstCell C i) := firstCell_definable B' C hC i
  let I := fun i => indicator h00 B' k (firstCell C i) (hPi i)
  let w := fun i => pointwiseProduct k f (I i)
  have hsum : (∑ i : Fin m, w i) = f := by
    apply eval_injective k
    funext z
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective z
    change (∑ i : Fin m, w i) (toPaperGamma γ) = f (toPaperGamma γ)
    simp only [eval_finsetSum, w, pointwiseProduct_eval, I, indicator_eval]
    rw [← Finset.mul_sum]
    have hex : ∃ i, γ ∈ C i := by
      obtain ⟨i, hi⟩ := hcover γ (Set.mem_univ γ)
      exact ⟨i, Set.mem_univ γ, hi⟩
    have he : (∑ i : Fin m, if γ ∈ firstCell C i then (1 : ℤ) else 0) = 1 := by
      simpa only [hex, ite_true] using firstCell_sum C γ
    rw [he, mul_one]
  have hcompat : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ x : Values.Gamma (M := M),
      w i (Additive.ofMul x) ≠ 0 → T x ^ q i = c i * x ^ p i := by
    intro i _ x hn
    change w i (toPaperGamma x) ≠ 0 at hn
    have hx : x ∈ firstCell C i := by
      by_contra hx
      apply hn
      simp only [w, pointwiseProduct_eval, I, indicator_eval, hx, ite_false, mul_zero]
    exact hx.1.2
  obtain ⟨P, hP, htotal, hprojection⟩ := exists_power_law_projection
    (G := Values.Gamma (M := M)) k Finset.univ p q c hq T w hcompat
  rw [hsum] at hP htotal hprojection
  exact ⟨P, hP, htotal, hprojection⟩

end DiamondIntegral.Section4.GammaUnaryProjection
