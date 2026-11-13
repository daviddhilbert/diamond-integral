import «section 4».GammaFibreCounting
import «section 4».EulerPowerLawFibres
import «section 4».GammaUnaryBijections

/-! Original-base descent of unary Euler image functions. Large fibres
occur at finitely many Gamma values; bounded counting treats all other
fibres. Every subset of the finite exceptional set is definable over the
original base, since finite ordered Gamma sets have definable elements.
Auxiliary power-law coefficients do not enter the conclusion's base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaUnaryDescent
open GammaOrderLogic GammaFibreCounting GammaDefinableFunctions GammaDefinableEuler
open GammaEulerSets EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem finite_subset_definable (B : Base (M := M))
    (Y : Set (Values.Gamma (M := M))) (hY : Y.Finite) (hYd : GammaDefinableOverBase B Y)
    (W : Set (Values.Gamma (M := M))) (hWY : W ⊆ Y) : GammaDefinableOverBase B W := by
  have hW : W.Finite := hY.subset hWY
  have hnames (y : Values.Gamma (M := M)) (hy : y ∈ hW.toFinset) :
      GammaDefinableOverBase B {y} := by
    apply gamma_finset_element_definable_base B hY.toFinset
    · simpa only [Set.Finite.coe_toFinset] using hYd
    · exact hY.mem_toFinset.mpr (hWY (hW.mem_toFinset.mp hy))
  have h := finite_union_definable_base B hW.toFinset (fun y => {y}) hnames
  have he : (⋃ y ∈ hW.toFinset, ({y} : Set (Values.Gamma (M := M)))) = W := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact hW.mem_toFinset.mp ha
    · intro hy
      exact ⟨y, hW.mem_toFinset.mpr hy, rfl⟩
  rwa [he] at h

theorem unary_union_definable (B : Base (M := M))
    (A C : Set (Values.Gamma (M := M))) (hA : GammaDefinableOverBase B A)
    (hC : GammaDefinableOverBase B C) : GammaDefinableOverBase B (A ∪ C) := by
  apply (unary_definable_iff B _).mp
  exact GammaQuantifierLogic.union_definable_base B _ _
    ((unary_definable_iff B A).mpr hA) ((unary_definable_iff B C).mpr hC)

theorem integerDefinable_of_counting (B : Base (M := M))
    (R : Set (Fin 2 → Values.Gamma (M := M))) (hR : GammaDefinable B R) (N : ℕ)
    (hY : {y | AtLeast R (N + 1) y}.Finite) (f : Values.Gamma (M := M) → ℤ)
    (hfr : (Set.range f).Finite)
    (hf : ∀ y, ¬ AtLeast R (N + 1) y → f y = ({x | ![x, y] ∈ R}.ncard : ℤ)) :
    IntegerDefinable B f := by
  refine ⟨hfr, ?_⟩
  intro z
  let Y : Set (Values.Gamma (M := M)) := {y | AtLeast R (N + 1) y}
  have hYd : GammaDefinableOverBase B Y := atLeast_definable_base B R hR (N + 1)
  let V (n : Fin (N + 1)) : Set (Values.Gamma (M := M)) :=
    if (n.val : ℤ) = z then {y | AtLeast R n.val y ∧ ¬ AtLeast R (n.val + 1) y} \ Y else ∅
  have hV (n : Fin (N + 1)) : GammaDefinableOverBase B (V n) := by
    by_cases hn : (n.val : ℤ) = z
    · simpa only [V, ite_eq_left hn] using (exactly_definable_base B R hR n.val).sdiff hYd
    · simpa only [V, ite_eq_right hn] using GammaDefinableFunctions.empty_definable_base B
  let W : Set (Values.Gamma (M := M)) := {y | y ∈ Y ∧ f y = z}
  have hW : GammaDefinableOverBase B W :=
    finite_subset_definable B Y hY hYd W (fun _ h => h.1)
  have hU := unary_union_definable B (⋃ n ∈ Finset.univ, V n) W
    (finite_union_definable_base B Finset.univ V (fun n _ => hV n)) hW
  convert hU using 1
  ext y
  change f y = z ↔ y ∈ (⋃ n ∈ Finset.univ, V n) ∪ W
  constructor
  · intro hy
    by_cases hyY : y ∈ Y
    · exact Or.inr ⟨hyY, hy⟩
    · obtain ⟨hfin, hcard⟩ := (atMost_iff R N y).mp hyY
      let n : Fin (N + 1) := ⟨{x | ![x, y] ∈ R}.ncard, Nat.lt_succ_of_le hcard⟩
      have hn : (n.val : ℤ) = z := (hf y hyY).symm.trans hy
      refine Or.inl (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨Finset.mem_univ n, ?_⟩⟩)
      simp only [V, ite_eq_left hn]
      exact ⟨(exactly_iff R n.val y).mpr ⟨hfin, rfl⟩, hyY⟩
  · intro hy
    rcases hy with hy | hy
    · obtain ⟨n, hyN⟩ := Set.mem_iUnion.mp hy
      obtain ⟨_, hyn⟩ := Set.mem_iUnion.mp hyN
      change y ∈ V n at hyn
      by_cases hnz : (n.val : ℤ) = z
      · simp only [V, ite_eq_left hnz] at hyn
        obtain ⟨_, hc⟩ := (exactly_iff R n.val y).mp hyn.1
        exact (hf y hyn.2).trans ((congrArg (fun a : ℕ => (a : ℤ)) hc).trans hnz)
      · simp only [V, ite_eq_right hnz, Set.notMem_empty] at hyn
    · exact hy.2

theorem exists_definable_power_law_image (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (k : EulerKind)
    (D : Set (Values.Gamma (M := M))) (hD : GammaDefinableOverBase B D)
    (T : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | z 0 ∈ D ∧ T (z 0) = z 1})
    {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) (c : Fin m → Values.Gamma (M := M))
    (hq : ∀ i, q i ≠ 0) (hcover : ∀ x ∈ D, ∃ i, T x ^ q i = c i * x ^ p i) :
    ∃ P : EulerFunction k (PaperGamma (M := M)),
      IntegerDefinable B (fun y => P (toPaperGamma y)) ∧
      ∃ F : PaperGamma (M := M) → EulerFunction k (PaperGamma (M := M)),
        (∀ y x : Values.Gamma (M := M), F (toPaperGamma y) (toPaperGamma x) =
          if x ∈ D ∧ T x = y then 1 else 0) ∧
        (∀ y : Values.Gamma (M := M), P (toPaperGamma y) = totalEuler k (F (toPaperGamma y))) ∧
        totalEuler k P = eulerValue h00 B k D hD := by
  obtain ⟨P, F, hF, hP, hEuler⟩ :=
    GammaUnaryPowerPushforward.exists_power_law_image h00 B k D hD T hT p q c hq hcover
  let R : Set (Fin 2 → Values.Gamma (M := M)) := {z | z 0 ∈ D ∧ T (z 0) = z 1}
  have hY : {y | AtLeast R (m + 1) y}.Finite :=
    finite_large_power_law_fibres D T p q c hq hcover
  have hfr : (Set.range (fun y => P (toPaperGamma y))).Finite :=
    (finite_range k P).subset (by rintro _ ⟨y, rfl⟩; exact ⟨toPaperGamma y, rfl⟩)
  have hd := integerDefinable_of_counting B R hT m hY (fun y => P (toPaperGamma y)) hfr
    (by
      intro y hy
      obtain ⟨hf, _⟩ := (atMost_iff R m y).mp hy
      rw [hP]
      apply totalEuler_finite_set_equiv k {x | ![x, y] ∈ R} hf toPaperGamma
        (F (toPaperGamma y))
      intro x
      by_cases hx : x ∈ D ∧ T x = y <;> simp [hF, R, hx])
  exact ⟨P, hd, F, hF, hP, hEuler⟩

theorem exists_unary_definable_image (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (B : Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (D : Set (Values.Gamma (M := M))) (hD : GammaDefinableOverBase B D)
    (T : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | z 0 ∈ D ∧ T (z 0) = z 1}) :
    ∃ P : EulerFunction k (PaperGamma (M := M)),
      IntegerDefinable B (fun y => P (toPaperGamma y)) ∧
      ∃ F : PaperGamma (M := M) → EulerFunction k (PaperGamma (M := M)),
        (∀ y x : Values.Gamma (M := M), F (toPaperGamma y) (toPaperGamma x) =
          if x ∈ D ∧ T x = y then 1 else 0) ∧
        (∀ y : Values.Gamma (M := M), P (toPaperGamma y) = totalEuler k (F (toPaperGamma y))) ∧
        totalEuler k P = eulerValue h00 B k D hD := by
  have hTc := GammaBaseExtension.to_common_real_syntax B _ hT
  obtain ⟨m, p, q, c, hq, hcover⟩ := linear h00 (commonRealNames B)
    (GammaUnaryBijections.nontrivial_commonBase B hΓ) D T hTc
  exact exists_definable_power_law_image h00 B k D hD T hT p q c hq hcover

end DiamondIntegral.Section4.GammaUnaryDescent
