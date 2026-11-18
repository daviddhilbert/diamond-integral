import «section 4».GermJumps
import «section 4».GammaBoundaryConstancy
import «section 4».GammaFamilyBoundary
import «section 4».Section3GammaCodeBridge
import «section 3».GammaGroundGammaAffineClassification
import «section 3».GammaGroundGammaSemiring
import «section 3».GammaGroundGammaProductDecomposition
import «section 3».GammaGroundTails
import Mathlib.Algebra.DualNumber

/-! An odd endpoint invariant of definable unary Gamma sets over the
complete Gamma ground. For a subgroup `T` containing all translation
constants of Gamma morphisms (values of ground-definable RV units) and an
element `δ`, the weight `chi T δ` is `+1` on `δT`, `-1` on `δ⁻¹T`; the
invariant sums germ jumps of the pieces against this weight. By the
piecewise unimodular classification of Gamma morphisms (which uses the
accepted Reichstein--Youssin input, Remark 3.15) it is invariant under
Gamma isomorphisms in degree one. Together with point counts in degree
zero it gives a semiring map from the positive Gamma semiring to the dual
numbers `ℤ[ε]`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section4.ResiduePurity
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.GammaEndpointInvariant
open GermJumps GammaOrderLogic

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-! ### Order facts on Gamma -/

theorem gamma_exists_gt (x : Values.Gamma (M := M)) : ∃ y, x < y := by
  obtain ⟨g, hg⟩ := exists_ne (1 : Values.Gamma (M := M))
  rcases lt_or_gt_of_ne hg with h | h
  · exact ⟨x * g⁻¹, by simpa using (mul_lt_mul_iff_left x).mpr (one_lt_inv'.mpr h)⟩
  · exact ⟨x * g, by simpa using (mul_lt_mul_iff_left x).mpr h⟩

theorem gamma_exists_lt (x : Values.Gamma (M := M)) : ∃ y, y < x := by
  obtain ⟨y, hy⟩ := gamma_exists_gt x⁻¹
  exact ⟨y⁻¹, inv_lt'.mp hy⟩

instance gammaNoMaxOrder : NoMaxOrder (Values.Gamma (M := M)) := ⟨gamma_exists_gt⟩
instance gammaNoMinOrder : NoMinOrder (Values.Gamma (M := M)) := ⟨gamma_exists_lt⟩

/-! ### Lines and tameness -/

/-- The diagonal line of a set of Gamma tuples; for unary tuples this is
the set itself read in Gamma. -/
def line {k : ℕ} (I : Set (Fin k → Values.Gamma (M := M))) : Set (Values.Gamma (M := M)) :=
  {x | (fun _ => x) ∈ I}

theorem cons_elim0_eq (x : Values.Gamma (M := M)) (y : Fin 0 → Values.Gamma (M := M)) :
    (Fin.cons x y : Fin 1 → Values.Gamma (M := M)) = fun _ => x := by
  funext i
  fin_cases i
  rfl

theorem exists_right_gap (F : Set (Values.Gamma (M := M))) (hF : F.Finite) (e : Values.Gamma (M := M)) :
    ∃ u, e < u ∧ ∀ t, e < t → t < u → t ∉ F := by
  by_cases hne : (F ∩ Set.Ioi e).Nonempty
  · obtain ⟨u, ⟨huF, hue⟩, hmin⟩ := Set.exists_min_image (F ∩ Set.Ioi e) id (hF.inter_of_left _) hne
    exact ⟨u, hue, fun t ht htu htF => absurd (hmin t ⟨htF, ht⟩) (not_le.mpr htu)⟩
  · obtain ⟨u, hu⟩ := gamma_exists_gt e
    exact ⟨u, hu, fun t ht _ htF => hne ⟨t, htF, ht⟩⟩

theorem exists_left_gap (F : Set (Values.Gamma (M := M))) (hF : F.Finite) (e : Values.Gamma (M := M)) :
    ∃ l, l < e ∧ ∀ t, l < t → t < e → t ∉ F := by
  by_cases hne : (F ∩ Set.Iio e).Nonempty
  · obtain ⟨l, ⟨hlF, hle⟩, hmax⟩ := Set.exists_max_image (F ∩ Set.Iio e) id (hF.inter_of_left _) hne
    exact ⟨l, hle, fun t hlt hte htF => absurd (hmax t ⟨htF, hte⟩) (not_le.mpr hlt)⟩
  · obtain ⟨l, hl⟩ := gamma_exists_lt e
    exact ⟨l, hl, fun t _ ht htF => hne ⟨t, htF, ht⟩⟩

/-- Definable unary Gamma sets over the complete Gamma ground are tame:
finitely many jumps (the intrinsic boundary is finite) and constant
membership between boundary points. -/
theorem tame_line (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (I : Set (Fin 1 → Values.Gamma (M := M))) (hI : GammaDefinable B I) : Tame (line I) := by
  let y0 : Fin 0 → Values.Gamma (M := M) := Fin.elim0
  have hmem : ∀ t, Fin.cons t y0 ∈ I ↔ t ∈ line I := by
    intro t
    rw [cons_elim0_eq]
    rfl
  let bd : Set (Values.Gamma (M := M)) := {x | Fin.cons x y0 ∈ GammaFamilyBoundary.Boundary (n := 0) I}
  obtain ⟨N, hN⟩ := GammaFamilyBoundary.uniform_boundary_bound h00 hκ hs B hr hγ (n := 0) I hI
  have hbd : bd.Finite := (hN y0).1
  have hconst : ∀ a b, (∀ t, a < t → t < b → t ∉ bd) → ∀ x z, a < x ∧ x < b → a < z ∧ z < b →
      (x ∈ line I ↔ z ∈ line I) := by
    intro a b hno x z hx hz
    rw [← hmem, ← hmem]
    exact GammaBoundaryConstancy.mem_iff_on_open_interval h00 B (n := 0) I hI y0 a b hno x z hx hz
  refine ⟨?_, ?_, ?_⟩
  · apply hbd.subset
    intro x hx
    by_contra hxb
    apply hx
    have hin : Fin.cons x y0 ∈ GammaFamilyBoundary.Interior I ∪ GammaFamilyBoundary.Interior Iᶜ := by
      by_contra h
      exact hxb h
    have hsub : ∀ (J : Set (Fin 1 → Values.Gamma (M := M))), Fin.cons x y0 ∈ GammaFamilyBoundary.Interior J →
        ∃ l u, l < x ∧ x < u ∧ ∀ t, l < t → t < u → (fun _ => t) ∈ J := by
      intro J ⟨l, u, hl, hu, h⟩
      refine ⟨l, u, hl, hu, fun t hlt htu => ?_⟩
      have := h t hlt htu
      have he : (Fin.cons t (fun j : Fin 0 => (Fin.cons x y0 : Fin 1 → Values.Gamma (M := M)) j.succ) :
          Fin 1 → Values.Gamma (M := M)) = fun _ => t := by
        funext i
        fin_cases i
        rfl
      rwa [he] at this
    rcases hin with h | h
    · obtain ⟨l, u, hl, hu, h⟩ := hsub I h
      have hR : RightIn (line I) x := ⟨u, hu, fun t ht => h t (hl.trans ht.1) ht.2⟩
      have hL : LeftIn (line I) x := ⟨l, hl, fun t ht => h t ht.1 (ht.2.trans hu)⟩
      simp only [jump, hR, hL, ite_true, sub_self]
    · obtain ⟨l, u, hl, hu, h⟩ := hsub Iᶜ h
      have hR : ¬ RightIn (line I) x := by
        rintro ⟨u', hu', h'⟩
        obtain ⟨t, ht1, ht2⟩ := exists_between (lt_min hu hu')
        exact h t (hl.trans ht1) (ht2.trans_le (min_le_left _ _)) (h' ⟨ht1, ht2.trans_le (min_le_right _ _)⟩)
      have hL : ¬ LeftIn (line I) x := by
        rintro ⟨l', hl', h'⟩
        obtain ⟨t, ht1, ht2⟩ := exists_between (max_lt hl hl')
        exact h t ((le_max_left _ _).trans_lt ht1) (ht2.trans hu) (h' ⟨(le_max_right _ _).trans_lt ht1, ht2⟩)
      simp only [jump, hR, hL, ite_false, sub_self]
  · intro e
    obtain ⟨u, hu, hno⟩ := exists_right_gap bd hbd e
    obtain ⟨x0, hx0⟩ := exists_between hu
    by_cases h0 : x0 ∈ line I
    · exact Or.inl ⟨u, hu, fun z hz => (hconst e u hno x0 z hx0 hz).mp h0⟩
    · exact Or.inr ⟨u, hu, fun z hz hzI => h0 ((hconst e u hno x0 z hx0 hz).mpr hzI)⟩
  · intro e
    obtain ⟨l, hl, hno⟩ := exists_left_gap bd hbd e
    obtain ⟨x0, hx0⟩ := exists_between hl
    by_cases h0 : x0 ∈ line I
    · exact Or.inl ⟨l, hl, fun z hz => (hconst l e hno x0 z hx0 hz).mp h0⟩
    · exact Or.inr ⟨l, hl, fun z hz hzI => h0 ((hconst l e hno x0 z hx0 hz).mpr hzI)⟩

theorem tame_piece (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (P : GammaGroundGammaPiece hc B 1) : Tame (line (k := 1) P.carrier) :=
  tame_line h00 hκ hs hr hγ P.carrier ((Section3GammaCodeBridge.native_iff P.carrier).mp P.definable)

/-! ### The odd weight -/

/-- `+1` on the coset `δT`, `-1` on `δ⁻¹T`. -/
def chi (T : Subgroup (Values.Gamma (M := M))) (δ e : Values.Gamma (M := M)) : ℤ :=
  (if δ⁻¹ * e ∈ T then 1 else 0) - (if δ * e ∈ T then 1 else 0)

theorem chi_mul (T : Subgroup (Values.Gamma (M := M))) (δ : Values.Gamma (M := M))
    {c : Values.Gamma (M := M)} (hc : c ∈ T) (e : Values.Gamma (M := M)) :
    chi T δ (c * e) = chi T δ e := by
  have h1 : δ⁻¹ * (c * e) ∈ T ↔ δ⁻¹ * e ∈ T := by
    rw [show δ⁻¹ * (c * e) = c * (δ⁻¹ * e) by ac_rfl]
    exact T.mul_mem_cancel_left hc
  have h2 : δ * (c * e) ∈ T ↔ δ * e ∈ T := by
    rw [show δ * (c * e) = c * (δ * e) by ac_rfl]
    exact T.mul_mem_cancel_left hc
  simp only [chi, if_congr h1 rfl rfl, if_congr h2 rfl rfl]

theorem chi_inv_mul (T : Subgroup (Values.Gamma (M := M))) (δ : Values.Gamma (M := M))
    {c : Values.Gamma (M := M)} (hc : c ∈ T) (e : Values.Gamma (M := M)) :
    chi T δ (c * e⁻¹) = - chi T δ e := by
  have h1 : δ⁻¹ * (c * e⁻¹) ∈ T ↔ δ * e ∈ T := by
    rw [← T.inv_mem_iff, show (δ⁻¹ * (c * e⁻¹))⁻¹ = c⁻¹ * (δ * e) by
      rw [mul_inv, mul_inv, inv_inv, inv_inv]; ac_rfl]
    exact T.mul_mem_cancel_left (T.inv_mem hc)
  have h2 : δ * (c * e⁻¹) ∈ T ↔ δ⁻¹ * e ∈ T := by
    rw [← T.inv_mem_iff, show (δ * (c * e⁻¹))⁻¹ = c⁻¹ * (δ⁻¹ * e) by
      rw [mul_inv, mul_inv, inv_inv]; ac_rfl]
    exact T.mul_mem_cancel_left (T.inv_mem hc)
  simp only [chi, if_congr h1 rfl rfl, if_congr h2 rfl rfl]
  ring

theorem chi_one (T : Subgroup (Values.Gamma (M := M))) (δ : Values.Gamma (M := M)) : chi T δ 1 = 0 := by
  have h : δ⁻¹ * 1 ∈ T ↔ δ * 1 ∈ T := by rw [mul_one, mul_one]; exact T.inv_mem_iff
  simp only [chi, if_congr h rfl rfl, sub_self]

theorem chi_self (T : Subgroup (Values.Gamma (M := M))) (δ : Values.Gamma (M := M)) (h : δ * δ ∉ T) :
    chi T δ δ = 1 := by
  have h1 : δ⁻¹ * δ ∈ T := by rw [inv_mul_cancel]; exact T.one_mem
  simp only [chi, h1, h, ite_true, ite_false, sub_zero]

/-! ### Upper rays -/

theorem rightIn_Ioi_iff (a e : Values.Gamma (M := M)) : RightIn (Set.Ioi a) e ↔ a ≤ e := by
  constructor
  · rintro ⟨u, hu, h⟩
    by_contra hlt
    push_neg at hlt
    obtain ⟨x, hx1, hx2⟩ := exists_between (lt_min hu hlt)
    exact absurd (h ⟨hx1, hx2.trans_le (min_le_left _ _)⟩) (not_lt.mpr (hx2.trans_le (min_le_right _ _)).le)
  · intro hae
    obtain ⟨u, hu⟩ := gamma_exists_gt e
    exact ⟨u, hu, fun x hx => hae.trans_lt hx.1⟩

theorem leftIn_Ioi_iff (a e : Values.Gamma (M := M)) : LeftIn (Set.Ioi a) e ↔ a < e := by
  constructor
  · rintro ⟨l, hl, h⟩
    obtain ⟨x, hx1, hx2⟩ := exists_between hl
    exact (h ⟨hx1, hx2⟩).trans hx2
  · intro hae
    exact ⟨a, hae, fun x hx => hx.1⟩

theorem jump_Ioi (a e : Values.Gamma (M := M)) : jump (Set.Ioi a) e = if e = a then 1 else 0 := by
  simp only [jump, rightIn_Ioi_iff, leftIn_Ioi_iff]
  by_cases h : e = a
  · subst h; simp
  · rcases lt_or_gt_of_ne h with h' | h'
    · simp [h, not_le.mpr h', not_lt.mpr h'.le]
    · simp [h, h'.le, h']

theorem weightedJump_Ioi (χ : Values.Gamma (M := M) → ℤ) (a : Values.Gamma (M := M)) :
    weightedJump χ (Set.Ioi a) = χ a := by
  unfold weightedJump
  rw [finsum_eq_single _ a (fun e he => by rw [jump_Ioi, if_neg he, zero_mul])]
  rw [jump_Ioi, if_pos rfl, one_mul]

/-! ### Affine maps of slope `±1` -/

def affEquiv (c : Values.Gamma (M := M)) (m : ℤ) : Values.Gamma (M := M) ≃ Values.Gamma (M := M) :=
  if m = 1 then Equiv.mulLeft c else (Equiv.inv _).trans (Equiv.mulLeft c)

theorem affEquiv_apply (c : Values.Gamma (M := M)) {m : ℤ} (hm : m = 1 ∨ m = -1) (x : Values.Gamma (M := M)) :
    affEquiv c m x = c * x ^ m := by
  rcases hm with rfl | rfl
  · simp [affEquiv]
  · simp [affEquiv]

theorem affEquiv_tame_weight (T : Subgroup (Values.Gamma (M := M))) (χ : Values.Gamma (M := M) → ℤ)
    (hχm : ∀ c ∈ T, ∀ e, χ (c * e) = χ e) (hχi : ∀ c ∈ T, ∀ e, χ (c * e⁻¹) = - χ e)
    {c : Values.Gamma (M := M)} (hc : c ∈ T) {m : ℤ} (hm : m = 1 ∨ m = -1)
    {A : Set (Values.Gamma (M := M))} (hA : Tame A) :
    Tame (affEquiv c m '' A) ∧ weightedJump χ (affEquiv c m '' A) = weightedJump χ A := by
  rcases hm with rfl | rfl
  · have hmono : StrictMono (affEquiv c 1) := by
      intro x y hxy
      simp only [affEquiv, if_pos rfl, Equiv.coe_mulLeft]
      exact (mul_lt_mul_iff_left c).mpr hxy
    exact ⟨hA.image_of_strictMono _ hmono,
      weightedJump_image_of_strictMono χ A _ hmono (fun e => by simp [affEquiv, hχm c hc])⟩
  · have hanti : StrictAnti (affEquiv c (-1)) := by
      intro x y hxy
      simp only [affEquiv, show ((-1 : ℤ) = 1) = False by simp, ite_false, Equiv.trans_apply,
        Equiv.inv_apply, Equiv.coe_mulLeft]
      exact (mul_lt_mul_iff_left c).mpr (inv_lt_inv_iff.mpr hxy)
    refine ⟨hA.image_of_strictAnti _ hanti, weightedJump_image_of_strictAnti χ A _ hanti (fun e => ?_)⟩
    simp only [affEquiv, show ((-1 : ℤ) = 1) = False by simp, ite_false, Equiv.trans_apply,
      Equiv.inv_apply, Equiv.coe_mulLeft]
    exact hχi c hc e

/-! ### The invariant on Gamma objects -/

/-- Translation constants of Gamma morphisms: values of ground-definable RV units. -/
def translationSubgroup (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    Subgroup (Values.Gamma (M := M)) :=
  Subgroup.closure {γ | ∃ c : Fin 1 → (CanonicalRV.RVSort M)ˣ,
    GammaGroundDefinable hc B (rawRVUnitSpace 1) {c} ∧ rvUnitValueHom (c 0) = γ}

def objNu (χ : Values.Gamma (M := M) → ℤ) {k : ℕ} (A : GammaGroundGammaObject hc B k) : ℤ :=
  ∑ i, weightedJump χ (line (k := k) (A.piece i).carrier)

/-- The line of a Gamma piece, avoiding carrier coercions in statements. -/
def pieceLine {k : ℕ} (P : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin k))) :
    Set (Values.Gamma (M := M)) :=
  line (k := k) P.carrier

theorem mem_pieceLine {k : ℕ} (P : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin k)))
    (x : Values.Gamma (M := M)) :
    x ∈ pieceLine P ↔ (show ((volumeGammaSpace hc).power (Fin k)).Carrier from fun _ => x) ∈ P.carrier :=
  Iff.rfl

theorem objNu_def (χ : Values.Gamma (M := M) → ℤ) {k : ℕ} (A : GammaGroundGammaObject hc B k) :
    objNu χ A = ∑ i, weightedJump χ (pieceLine (A.piece i)) := rfl

theorem tame_pieceLine (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (P : GammaGroundGammaPiece hc B 1) : Tame (pieceLine P) :=
  tame_piece h00 hκ hs hr hγ P

theorem matrix_entry_unit (A : Matrix (Fin 1) (Fin 1) ℤ) (h : IsUnit A.det) :
    A 0 0 = 1 ∨ A 0 0 = -1 := by
  rw [Matrix.det_fin_one] at h
  exact Int.isUnit_iff.mp h

/-- Invariance of the endpoint invariant under Gamma isomorphisms in degree one. -/
theorem objNu_iso [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin 1 → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (χ : Values.Gamma (M := M) → ℤ)
    (hχm : ∀ c ∈ translationSubgroup hc B, ∀ e, χ (c * e) = χ e)
    (hχi : ∀ c ∈ translationSubgroup hc B, ∀ e, χ (c * e⁻¹) = - χ e)
    {A D : GammaGroundGammaObject hc B 1} (g : GammaGroundGammaHom A D) :
    objNu χ A = objNu χ D := by
  have hg := gammaGroundGammaHom_piecewiseGLZ hκ hs h00 hsmall hγsmall RY g
  let F := g.bijection
  have htame : ∀ P : GammaGroundGammaPiece hc B 1, Tame (line (k := 1) P.carrier) :=
    tame_piece h00 hκ.le hs hsmall hγsmall
  choose N Fm P hPsub hcover hform using hg
  let c : ∀ i j, Fin (N i j) → Values.Gamma (M := M) := fun i j q => rvUnitValueHom ((Fm i j q).coefficient 0)
  have hcT : ∀ i j q, c i j q ∈ translationSubgroup hc B := fun i j q =>
    Subgroup.subset_closure ⟨(Fm i j q).coefficient, (Fm i j q).coefficient_definable, rfl⟩
  let m : ∀ i j, Fin (N i j) → ℤ := fun i j q => (Fm i j q).matrix 0 0
  have hm : ∀ i j q, m i j q = 1 ∨ m i j q = -1 := fun i j q =>
    matrix_entry_unit _ (Fm i j q).det_unit
  let S : ∀ i j, Fin (N i j) → Set (Values.Gamma (M := M)) := fun i j q => line (k := 1) (P i j q).carrier
  let Tset : ∀ i j, Fin (N i j) → Set (Values.Gamma (M := M)) := fun i j q => affEquiv (c i j q) (m i j q) '' S i j q
  -- pointwise formula
  have hpt : ∀ i j q (γ : F.toFamilyMap.branchSource i j), γ.val ∈ (P i j q).carrier →
      ((F.toFamilyMap.branchMap i j) γ).val 0 = affEquiv (c i j q) (m i j q) (γ.val 0) := by
    intro i j q γ hγ
    have h := congrFun (hform i j q γ hγ) 0
    rw [affEquiv_apply _ (hm i j q)]
    rw [h]
    simp only [Pi.mul_apply, rvUnitTupleValues, integerMonomialMap, Fin.prod_univ_one]
    rfl
  have hfun : ∀ (γ : Fin 1 → Values.Gamma (M := M)), γ = fun _ => γ 0 := by
    intro γ; funext i; fin_cases i; rfl
  -- source decomposition
  have hsrc : ∀ i, weightedJump χ (line (k := 1) (A.piece i).carrier) = ∑ j, ∑ q, weightedJump χ (S i j q) := by
    intro i
    rw [← Fintype.sum_sigma (fun p : (Σ j, Fin (N i j)) => weightedJump χ (S i p.1 p.2))]
    apply weightedJump_partition χ _ (fun p : (Σ j, Fin (N i j)) => S i p.1 p.2)
      (fun p => htame _)
    · rintro ⟨j, q⟩ ⟨j', q'⟩ hne
      rw [Set.disjoint_left]
      intro x hx hx'
      apply hne
      have hj : x ∈ line (k := 1) (F.toFamilyMap.branchSource i j).carrier := hPsub i j q hx
      have hj' : x ∈ line (k := 1) (F.toFamilyMap.branchSource i j').carrier := hPsub i j' q' hx'
      let a : A.piece i := ⟨fun _ => x, F.toFamilyMap.branchSource_subset i j hj⟩
      obtain ⟨j0, _, huniq⟩ := F.toFamilyMap.branchSource_partition i a
      have e1 := huniq j hj
      have e2 := huniq j' hj'
      subst e1
      cases e2
      obtain ⟨q0, _, hq⟩ := hcover i j ⟨fun _ => x, hj⟩
      have e3 := hq q hx
      have e4 := hq q' hx'
      subst e3
      cases e4
      rfl
    · ext x
      simp only [Set.mem_iUnion]
      constructor
      · intro hx
        let a : A.piece i := ⟨fun _ => x, hx⟩
        obtain ⟨j, hj, _⟩ := F.toFamilyMap.branchSource_partition i a
        obtain ⟨q, hq, _⟩ := hcover i j ⟨fun _ => x, hj⟩
        exact ⟨⟨j, q⟩, hq⟩
      · rintro ⟨⟨j, q⟩, hx⟩
        exact F.toFamilyMap.branchSource_subset i j (hPsub i j q hx)
  -- target decomposition
  have htgt : ∀ j, weightedJump χ (line (k := 1) (D.piece j).carrier) = ∑ i, ∑ q, weightedJump χ (S i j q) := by
    intro j
    have hTS : ∀ i q, Tame (Tset i j q) ∧ weightedJump χ (Tset i j q) = weightedJump χ (S i j q) :=
      fun i q => affEquiv_tame_weight _ χ hχm hχi (hcT i j q) (hm i j q) (htame _)
    rw [← Fintype.sum_sigma (fun p : (Σ i, Fin (N i j)) => weightedJump χ (S p.1 j p.2))]
    rw [← Finset.sum_congr rfl (fun p _ => (hTS p.1 p.2).2)]
    apply weightedJump_partition χ _ (fun p : (Σ i, Fin (N i j)) => Tset p.1 j p.2)
      (fun p => (hTS p.1 p.2).1)
    · rintro ⟨i, q⟩ ⟨i', q'⟩ hne
      rw [Set.disjoint_left]
      rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxy⟩
      apply hne
      let a : F.toFamilyMap.branchSource i j := ⟨fun _ => x, hPsub i j q hx⟩
      let a' : F.toFamilyMap.branchSource i' j := ⟨fun _ => x', hPsub i' j q' hx'⟩
      have hva : ((F.toFamilyMap.branchMap i j) a).val = fun _ => affEquiv (c i j q) (m i j q) x := by
        rw [hfun ((F.toFamilyMap.branchMap i j) a).val, hpt i j q a hx]
      have hva' : ((F.toFamilyMap.branchMap i' j) a').val = fun _ => affEquiv (c i j q) (m i j q) x := by
        rw [hfun ((F.toFamilyMap.branchMap i' j) a').val, hpt i' j q' a' hx', hxy]
      let b : D.piece j := ⟨fun _ => affEquiv (c i j q) (m i j q) x,
        hva ▸ ((F.toFamilyMap.branchMap i j) a).property⟩
      obtain ⟨i0, _, huniq⟩ := F.branchImage_partition j b
      have e1 := huniq i ⟨a, hva⟩
      have e2 := huniq i' ⟨a', hva'⟩
      subst e1
      cases e2
      have haa : a = a' := F.toFamilyMap.branchMap_injective F.equiv.injective i j
        (Subtype.ext (hva.trans hva'.symm))
      have hxx : x = x' := congrFun (congrArg Subtype.val haa) 0
      subst hxx
      obtain ⟨q0, _, hq⟩ := hcover i j a
      have e3 := hq q hx
      have e4 := hq q' hx'
      subst e3
      cases e4
      rfl
    · ext y
      simp only [Set.mem_iUnion]
      constructor
      · intro hy
        let b : D.piece j := ⟨fun _ => y, hy⟩
        obtain ⟨i, ⟨a, ha⟩, _⟩ := F.branchImage_partition j b
        obtain ⟨q, hq, _⟩ := hcover i j a
        refine ⟨⟨i, q⟩, a.val 0, ?_, ?_⟩
        · change (fun _ => a.val 0) ∈ (P i j q).carrier
          rw [← hfun a.val]
          exact hq
        · rw [← hpt i j q a hq]
          exact congrFun ha 0
      · rintro ⟨⟨i, q⟩, x, hx, rfl⟩
        let a : F.toFamilyMap.branchSource i j := ⟨fun _ => x, hPsub i j q hx⟩
        have hva : ((F.toFamilyMap.branchMap i j) a).val = fun _ => affEquiv (c i j q) (m i j q) x := by
          rw [hfun ((F.toFamilyMap.branchMap i j) a).val, hpt i j q a hx]
        change (fun _ => affEquiv (c i j q) (m i j q) x) ∈ (D.piece j).carrier
        rw [← hva]
        exact ((F.toFamilyMap.branchMap i j) a).property
  unfold objNu
  rw [Finset.sum_congr rfl (fun i _ => hsrc i), Finset.sum_congr rfl (fun j _ => htgt j)]
  exact Finset.sum_comm

end DiamondIntegral.Section4.GammaEndpointInvariant
