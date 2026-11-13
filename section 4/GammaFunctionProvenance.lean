import «section 4».GammaOrderLogic
import «section 4».GammaDefinableEuler
import «section 4».EulerBreakpoints

/-! Canonical finite-jump coefficients have thresholds definable over the
original base. The proof first defines the intrinsic finite breakpoint set,
then uses the checked minimum-erasure proof for finite ordered Gamma sets. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFunctionProvenance
open GammaOrderLogic GammaDefinableEuler EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem constantNear_eq_union_interiors (f : Values.Gamma (M := M) → ℤ)
    (hf : (Set.range f).Finite) :
    {a | ConstantNear f a} = ⋃ m ∈ hf.toFinset, Interior {x | f x = m} := by
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨l, u, hla, hau, h⟩
    exact ⟨f a, hf.mem_toFinset.mpr ⟨a, rfl⟩, l, u, hla, hau, h⟩
  · rintro ⟨m, _, l, u, hla, hau, h⟩
    refine ⟨l, u, hla, hau, ?_⟩
    intro x hlx hxu
    exact (h x hlx hxu).trans (h a hla hau).symm

theorem constantNear_definable_base (B : Base (M := M))
    (f : Values.Gamma (M := M) → ℤ) (hf : (Set.range f).Finite)
    (hd : ∀ m : ℤ, GammaDefinableOverBase B {γ | f γ = m}) :
    GammaDefinableOverBase B {γ | ConstantNear f γ} := by
  rw [constantNear_eq_union_interiors f hf]
  exact finite_union_definable_base B hf.toFinset _
    (fun m _ => interior_definable_base B _ (hd m))

theorem breakpoint_definable_base (B : Base (M := M)) (k : EulerKind)
    (g : EulerFunction k (PaperGamma (M := M)))
    (hd : ∀ m : ℤ, GammaDefinableOverBase B {γ | g (toPaperGamma γ) = m})
    (a : PaperGamma (M := M)) (ha : a ∈ breakpoints k g) :
    GammaDefinableClosureAtBase B (toPaperGamma.symm a) := by
  let f : Values.Gamma (M := M) → ℤ := fun γ => g (toPaperGamma γ)
  let F : Finset (Values.Gamma (M := M)) := breakpoints (Γ := PaperGamma (M := M)) k g
  have hset : (F : Set (Values.Gamma (M := M))) = {γ | ¬ ConstantNear f γ} := by
    ext γ
    exact mem_breakpoints_iff (Γ := PaperGamma (M := M)) k g (toPaperGamma γ)
  have hF : GammaDefinableOverBase B (F : Set (Values.Gamma (M := M))) := by
    rw [hset]
    exact complement_definable_base B {γ | ConstantNear f γ}
      (constantNear_definable_base B f (finite_range (Γ := PaperGamma (M := M)) k g) hd)
  exact gamma_finset_element_definable_base B F hF (toPaperGamma.symm a) ha

theorem coefficient_threshold_definable_base (B : Base (M := M)) (k : EulerKind)
    (g : EulerFunction k (PaperGamma (M := M)))
    (hd : ∀ m : ℤ, GammaDefinableOverBase B {γ | g (toPaperGamma γ) = m})
    (a : PaperGamma (M := M))
    (ha : ((coefficientEquiv k).symm g).2.1 a ≠ 0 ∨
      ((coefficientEquiv k).symm g).2.2 a ≠ 0) :
    GammaDefinableClosureAtBase B (toPaperGamma.symm a) := by
  apply breakpoint_definable_base B k g hd a
  change a ∈ ((coefficientEquiv k).symm g).2.1.support ∪
    ((coefficientEquiv k).symm g).2.2.support
  simpa only [Finset.mem_union, Finsupp.mem_support_iff] using ha

theorem definable_function_coefficients (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (k : EulerKind) (f : PaperGamma (M := M) → ℤ)
    (hf : (Set.range f).Finite)
    (hd : ∀ m : ℤ, GammaDefinableOverBase B {γ | f (toPaperGamma γ) = m}) :
    ∃ v : StepCoefficients (PaperGamma (M := M)), stepEval v = f ∧
      ∀ a, v.2.1 a ≠ 0 ∨ v.2.2 a ≠ 0 →
        GammaDefinableClosureAtBase B (toPaperGamma.symm a) := by
  obtain ⟨g, hg⟩ := exists_eulerFunction_of_definable h00 B k f hf hd
  have he : (g : PaperGamma (M := M) → ℤ) = f := funext hg
  refine ⟨(coefficientEquiv k).symm g, ?_, ?_⟩
  · exact (funext (coefficients_eval k g)).trans he
  · intro a ha
    apply coefficient_threshold_definable_base B k g _ a ha
    intro m
    simpa only [he] using hd m

end DiamondIntegral.Section4.GammaFunctionProvenance
