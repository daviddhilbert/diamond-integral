import «section 2».CitedGammaLinearity
import «section 2».GammaPowerRadii

/-! Remark 2.47: curve selection fails in `Γ_∞`. The set `Γ × (0, ∞) ⊆ Γ_∞²`
contains curves approaching `(0, 0)` and `(∞, ∞)` (the diagonal), but no
definable curve approaches `(∞, 0)`. Every definable one-parameter function
is piecewise rational-affine (the cited input used for 2.41): on a bounded
parameter range the first coordinate stays bounded, and off it the second
coordinate is either constant or far from `0`.

In the multiplicative notation of the formalization, `0 ∈ Γ` is `1`, the
interval `(0, ∞)` is `{γ | 1 < γ}`, and "tending to `∞`" means exceeding
every element. The checked statement is stronger than non-convergence:
`remark_2_47` gives `N` and `ε > 1` such that `h t ≥ ε` whenever `f t > N`,
so the points of the curve do not even accumulate at `(∞, 0)`
(`remark_2_47_no_approach`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_gamma_gt_one {B : ParameterBase M} (hΓ : NontrivialDefinableGamma B) :
    ∃ g : Gamma M, 1 < g := by
  obtain ⟨γ,δ,_,_,hne⟩ := hΓ
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨δ / γ,one_lt_div'.mpr h⟩
  · exact ⟨γ / δ,one_lt_div'.mpr h⟩

/-- A rational-affine law with nonzero slope has bounded sources over bounded
values. -/
theorem gamma_power_law_source_bounded (A : Set (Gamma M)) (hA : BddAbove A ∧ BddBelow A)
    (p : ℤ) (hp : p ≠ 0) (q : ℕ) (c : Gamma M) :
    BddAbove {x | ∃ y ∈ A, y ^ q = c * x ^ p} ∧ BddBelow {x | ∃ y ∈ A, y ^ q = c * x ^ p} := by
  cases p with
  | ofNat n =>
    have hn : n ≠ 0 := fun h => hp (by rw [h]; rfl)
    have hs := gammaPowerRelationImage_bounded A hA (q : ℤ) n hn c⁻¹
    have hsub : {x | ∃ y ∈ A, y ^ q = c * x ^ (Int.ofNat n)} ⊆ gammaPowerRelationImage A (q : ℤ) n c⁻¹ := by
      rintro x ⟨y,hy,hl⟩
      refine ⟨y,hy,?_⟩
      have hl' : y ^ q = c * x ^ n := by simpa only [Int.ofNat_eq_natCast,zpow_natCast] using hl
      rw [zpow_natCast,hl',inv_mul_cancel_left]
    exact ⟨hs.1.mono hsub,hs.2.mono hsub⟩
  | negSucc n =>
    have hs := gammaPowerRelationImage_bounded A hA (-(q : ℤ)) (n+1) (Nat.succ_ne_zero n) c
    have hsub : {x | ∃ y ∈ A, y ^ q = c * x ^ (Int.negSucc n)} ⊆
        gammaPowerRelationImage A (-(q : ℤ)) (n+1) c := by
      rintro x ⟨y,hy,hl⟩
      refine ⟨y,hy,?_⟩
      rw [zpow_negSucc] at hl
      rw [zpow_neg,zpow_natCast,hl,mul_inv_rev,inv_inv,mul_comm (x ^ (n+1)) c⁻¹,mul_inv_cancel_left]
    exact ⟨hs.1.mono hsub,hs.2.mono hsub⟩

/-- Remark 2.47. Let `t ↦ (f t, h t)` be a definable curve on `D ⊆ Γ` with
values in `Γ × (0, ∞)`. Then there are `N` and `ε > 0` such that `h t ≥ ε`
whenever `f t > N`: the curve stays away from `(∞, 0)`. -/
theorem remark_2_47 (h00 : M ⊨ Axioms.ACVF00) (linear : GammaPiecewiseRationalAffineInput (M := M))
    (S : Set M) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Gamma M)) (f h : Gamma M → Gamma M)
    (hf : GammaSyntax.Definable S (fun z : Fin 2 → Gamma M => z 0 ∈ D ∧ f (z 0) = z 1))
    (hh : GammaSyntax.Definable S (fun z : Fin 2 → Gamma M => z 0 ∈ D ∧ h (z 0) = z 1))
    (hpos : ∀ t ∈ D, 1 < h t) :
    ∃ N ε : Gamma M, 1 < ε ∧ ∀ t ∈ D, N < f t → ε ≤ h t := by
  classical
  obtain ⟨g,hg⟩ := exists_gamma_gt_one hΓ
  obtain ⟨k,p,q,c,hq,hcover⟩ := linear h00 S hΓ D h hh
  obtain ⟨k',p',q',c',hq',hcover'⟩ := linear h00 S hΓ D f hf
  -- On a law of slope zero the second coordinate is a fixed value.
  let e (i : Fin k) := gammaPowerOrderIso (M := M) (q i) (hq i)
  let v (i : Fin k) : Gamma M := (e i).symm (c i)
  have hv : ∀ i, ∀ t ∈ D, p i = 0 → h t ^ q i = c i * t ^ p i → h t = v i := by
    intro i t _ hp hlaw
    rw [hp,zpow_zero,mul_one] at hlaw
    apply (e i).injective
    rw [(e i).apply_symm_apply]
    exact hlaw
  let T : Finset (Gamma M) := insert g ((Finset.univ.filter (fun i => p i = 0 ∧ 1 < v i)).image v)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  let ε := T.min' hT
  have hεT : ∀ x ∈ T, 1 < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hg
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2.2
  have hε : 1 < ε := hεT _ (Finset.min'_mem T hT)
  have hεg : ε ≤ g := Finset.min'_le T g (Finset.mem_insert_self _ _)
  -- Where the second coordinate is below `g` on a law of nonzero slope, the
  -- parameter is bounded.
  let W : Set (Gamma M) := ⋃ i : Fin k, {x | ∃ y ∈ Set.Icc (1 : Gamma M) g, p i ≠ 0 ∧ y ^ q i = c i * x ^ p i}
  have hI : BddAbove (Set.Icc (1 : Gamma M) g) ∧ BddBelow (Set.Icc (1 : Gamma M) g) :=
    ⟨bddAbove_Icc,bddBelow_Icc⟩
  have hWi : ∀ i : Fin k,
      BddAbove {x | ∃ y ∈ Set.Icc (1 : Gamma M) g, p i ≠ 0 ∧ y ^ q i = c i * x ^ p i} ∧
      BddBelow {x | ∃ y ∈ Set.Icc (1 : Gamma M) g, p i ≠ 0 ∧ y ^ q i = c i * x ^ p i} := by
    intro i
    by_cases hp : p i = 0
    · have he : {x | ∃ y ∈ Set.Icc (1 : Gamma M) g, p i ≠ 0 ∧ y ^ q i = c i * x ^ p i} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
        rintro ⟨y,_,hne,_⟩
        exact hne hp
      rw [he]
      exact ⟨bddAbove_empty,bddBelow_empty⟩
    · have hs := gamma_power_law_source_bounded _ hI (p i) hp (q i) (c i)
      have hsub : {x | ∃ y ∈ Set.Icc (1 : Gamma M) g, p i ≠ 0 ∧ y ^ q i = c i * x ^ p i} ⊆
          {x | ∃ y ∈ Set.Icc (1 : Gamma M) g, y ^ q i = c i * x ^ p i} := by
        rintro x ⟨y,hy,_,hl⟩
        exact ⟨y,hy,hl⟩
      exact ⟨hs.1.mono hsub,hs.2.mono hsub⟩
  have hW : BddAbove W ∧ BddBelow W :=
    ⟨(Set.finite_univ.bddAbove_biUnion).mpr (fun i _ => (hWi i).1) |>.mono
        (fun x hx => by
          obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_biUnion (Set.mem_univ i) hi),
      (Set.finite_univ.bddBelow_biUnion).mpr (fun i _ => (hWi i).2) |>.mono
        (fun x hx => by
          obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_biUnion (Set.mem_univ i) hi)⟩
  obtain ⟨K,hK⟩ := (gamma_symmetric_bound_iff W).mpr hW
  -- On that bounded parameter range the first coordinate is bounded.
  obtain ⟨N,hN⟩ := gamma_finite_power_laws_bounded (D ∩ Set.Icc K⁻¹ K)
    ⟨bddAbove_Icc.mono Set.inter_subset_right,bddBelow_Icc.mono Set.inter_subset_right⟩
    f p' q' hq' c' (fun x hx => hcover' x hx.1)
  refine ⟨N,ε,hε,fun t ht hNt => ?_⟩
  by_contra hlt
  have hlt' : h t < ε := not_le.mp hlt
  obtain ⟨i,hlaw⟩ := hcover t ht
  have hp : p i ≠ 0 := by
    intro hp
    have hti := hv i t ht hp hlaw
    have hvpos : 1 < v i := by
      rw [← hti]
      exact hpos t ht
    have hvT : v i ∈ T := Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp,hvpos⟩,rfl⟩)
    have hvlt : v i < ε := by
      rw [← hti]
      exact hlt'
    exact absurd (Finset.min'_le T _ hvT) (not_le.mpr hvlt)
  have htW : t ∈ W :=
    Set.mem_iUnion.mpr ⟨i,h t,⟨(hpos t ht).le,(hlt'.trans_le hεg).le⟩,hp,hlaw⟩
  have hb := (hN (f t) ⟨t,⟨ht,(hK t htW).1,(hK t htW).2⟩,rfl⟩).2
  exact (not_le.mpr hNt) hb

/-- Remark 2.47: no definable curve in `Γ × (0, ∞)` approaches `(∞, 0)`; its
points do not accumulate there. -/
theorem remark_2_47_no_approach (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    (S : Set M) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Gamma M)) (f h : Gamma M → Gamma M)
    (hf : GammaSyntax.Definable S (fun z : Fin 2 → Gamma M => z 0 ∈ D ∧ f (z 0) = z 1))
    (hh : GammaSyntax.Definable S (fun z : Fin 2 → Gamma M => z 0 ∈ D ∧ h (z 0) = z 1))
    (hpos : ∀ t ∈ D, 1 < h t)
    (happroach : ∀ N ε : Gamma M, 1 < ε → ∃ t ∈ D, N < f t ∧ h t < ε) : False := by
  obtain ⟨N,ε,hε,hfar⟩ := remark_2_47 h00 linear S hΓ D f h hf hh hpos
  obtain ⟨t,ht,hN,hε'⟩ := happroach N ε hε
  exact (not_le.mpr hε') (hfar t ht hN)

/-- The diagonal curve `t ↦ (t, t)` on `(0, ∞)` approaches both `(0, 0)` and
`(∞, ∞)`, so the failure is specific to the boundary point `(∞, 0)`. -/
theorem remark_2_47_diagonal {B : ParameterBase M} (hΓ : NontrivialDefinableGamma B) :
    (∀ ε : Gamma M, 1 < ε → ∃ t : Gamma M, 1 < t ∧ t < ε) ∧
    (∀ N : Gamma M, ∃ t : Gamma M, 1 < t ∧ N < t) := by
  obtain ⟨g,hg⟩ := exists_gamma_gt_one hΓ
  refine ⟨fun ε hε => ?_,fun N => ?_⟩
  · let e := gammaPowerOrderIso (M := M) 2 (by norm_num)
    let t := e.symm ε
    have ht : t ^ 2 = ε := e.apply_symm_apply ε
    have h1 : 1 < t := by
      by_contra hle
      have hle' : t ≤ 1 := not_lt.mp hle
      have : t ^ 2 ≤ 1 := pow_le_one' hle' 2
      rw [ht] at this
      exact (not_le.mpr hε) this
    refine ⟨t,h1,?_⟩
    calc t = t * 1 := (mul_one t).symm
      _ < t * t := (OrderIso.mulLeft t).strictMono h1
      _ = ε := by rw [← ht,pow_two]
  · refine ⟨max N 1 * g,?_,?_⟩
    · have h := (OrderIso.mulRight g).monotone (le_max_right N 1)
      change 1 * g ≤ max N 1 * g at h
      rw [one_mul] at h
      exact hg.trans_le h
    · calc N ≤ max N 1 := le_max_left N 1
        _ = max N 1 * 1 := (mul_one _).symm
        _ < max N 1 * g := (OrderIso.mulLeft (max N 1)).strictMono hg

end DiamondIntegral.Section2
