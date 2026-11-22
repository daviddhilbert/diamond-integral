import «section 8».TruncPairs

/-! Scaling a concrete set into `𝒪`.

Truncations are defined for points of `𝒪ⁿ`. A bounded set is first scaled by `t^L`:

* `scaleRaw L X = {(t^L x, u) | (x, u) ∈ X}` (`mem_mixedSet_scale`), definable over `ℂ((t))` when
  `X` is (`scaleRaw_definableOver`);
* `cf_tPow_mul`: `cf (t^L y) γ = cf y (γ - L)`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language HahnSeries
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section4 DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.RingDefinable DiamondIntegral.Section8.Hm

local instance scaleStructure : LRV.Structure Carrier := canonicalInterpret
local instance scaleModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-! ### Powers of `t` -/

theorem tPow_coe (L : ℕ) : ((tPow L : Ser) : HahnSeries ℚ ℂ) = single (L : ℚ) 1 := by
  have h := mono_coe 1 L 1
  have he : mono 1 L 1 = tPow L := by
    change puiseuxConstant 1 * puiseuxRoot 1 ^ L = puiseuxRoot 1 ^ L
    rw [map_one, one_mul]
  rw [he] at h
  rw [h, lev]
  simp

theorem cf_tPow_mul (L : ℕ) (y : Ser) (γ : ℚ) : cf (tPow L * y) γ = cf y (γ - L) := by
  have h : ((tPow L * y : Ser) : HahnSeries ℚ ℂ) = single (L : ℚ) 1 * (y : HahnSeries ℚ ℂ) := by
    change ((tPow L : Ser) : HahnSeries ℚ ℂ) * (y : HahnSeries ℚ ℂ) = _
    rw [tPow_coe]
  rw [cf, h]
  have he : γ = (γ - L) + L := by ring
  conv_lhs => rw [he]
  rw [coeff_single_mul_add, one_mul]
  rfl

theorem tPow_ne_zero (L : ℕ) : tPow L ≠ 0 := pow_ne_zero _ tS_ne_zero

/-- `t^{-L}`. -/
def tInv (L : ℕ) : Ser := (tPow L)⁻¹

theorem tInv_mem (L : ℕ) : baseCarrier (Sum.inl (tInv L) : Carrier) := by
  change (tPow L)⁻¹ ∈ puiseuxBaseSubfield ℂ
  exact inv_mem (tPow_mem L)

theorem tInv_mul_tPow (L : ℕ) (y : Ser) : tInv L * (tPow L * y) = y := by
  rw [tInv, ← mul_assoc, inv_mul_cancel₀ (tPow_ne_zero L), one_mul]

theorem tPow_mul_tInv (L : ℕ) (y : Ser) : tPow L * (tInv L * y) = y := by
  rw [tInv, ← mul_assoc, mul_inv_cancel₀ (tPow_ne_zero L), one_mul]

variable {n l : ℕ}

/-! ### Scaled points -/

/-- `(t^L x, u)`. -/
def scaleP (L : ℕ) (p : (Fin n → Ser) × (Fin l → RV)) : (Fin n → Ser) × (Fin l → RV) :=
  (fun i => tPow L * p.1 i, p.2)

/-- `(t^{-L} x, u)`. -/
def unscaleP (L : ℕ) (p : (Fin n → Ser) × (Fin l → RV)) : (Fin n → Ser) × (Fin l → RV) :=
  (fun i => tInv L * p.1 i, p.2)

theorem unscaleP_scaleP (L : ℕ) (p : (Fin n → Ser) × (Fin l → RV)) : unscaleP L (scaleP L p) = p :=
  Prod.ext (funext fun i => tInv_mul_tPow L (p.1 i)) rfl

theorem scaleP_unscaleP (L : ℕ) (p : (Fin n → Ser) × (Fin l → RV)) : scaleP L (unscaleP L p) = p :=
  Prod.ext (funext fun i => tPow_mul_tInv L (p.1 i)) rfl

/-! ### Scaled raw sets -/

/-- The polynomial `c X₀`. -/
def mulPoly (c : Ser) : MvPolynomial (Fin 1) (VFType (M := Carrier)) :=
  MvPolynomial.C (taggedFieldEquiv.symm c) * MvPolynomial.X 0

/-- The code of `c a`. -/
def mulCode (c : Ser) (a : Carrier) : Carrier :=
  SpecialTransformations.Section5.mvPolynomialCode (mulPoly c) (Sum.elim ![a] Fin.elim0)

theorem mulCode_inl (c x : Ser) : mulCode c (Sum.inl x) = Sum.inl (c * x) := by
  unfold mulCode
  have hcode := SpecialTransformations.Section5.mvPolynomialCode_eq (mulPoly c)
    (Sum.elim ![(Sum.inl x : Carrier)] Fin.elim0) ![vfOf x] (fun a => by fin_cases a; rfl)
  rw [hcode]
  have he : taggedFieldEquiv (MvPolynomial.eval ![vfOf x] (mulPoly c)) = c * x := by
    rw [mulPoly, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, map_mul]
    simp
  rw [← he]
  exact (vfType_tag _).symm

theorem mulPoly_coeff_mem (c : Ser) (hc : baseCarrier (Sum.inl c : Carrier)) (d : Fin 1 →₀ ℕ) :
    ((mulPoly c).coeff d).val ∈ {a : Carrier | baseCarrier a} := by
  rw [mulPoly, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
  split_ifs
  · rw [mul_one]
    exact base_mem_of c hc
  · rw [mul_zero]
    exact base_mem_of 0 (zero_mem _)

theorem mulCode_definable (c : Ser) (hc : baseCarrier (Sum.inl c : Carrier)) {K : ℕ} (i : Fin K) :
    {a : Carrier | baseCarrier a}.DefinableFun LRV (fun z : Fin K → Carrier => mulCode c (z i)) := by
  have hp := SpecialTransformations.Section5.mvPolynomialCode_definable (m := 0)
    (S := {a : Carrier | baseCarrier a}) (mulPoly c) (mulPoly_coeff_mem c hc)
  change @Set.DefinableFun Carrier LRV (CanonicalStructure.normalize (M := Carrier)) (Fin 1 ⊕ Fin 0)
    {a : Carrier | baseCarrier a} (SpecialTransformations.Section5.mvPolynomialCode (m := 0) (mulPoly c)) at hp
  rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical] at hp
  have hinner : {a : Carrier | baseCarrier a}.DefinableMap LRV
      (fun z : Fin K → Carrier => (Sum.elim ![z i] Fin.elim0 : Fin 1 ⊕ Fin 0 → Carrier)) := by
    intro a
    rcases a with a | a
    · fin_cases a
      exact Set.DefinableFun.proj LRV
    · exact a.elim0
  change {a : Carrier | baseCarrier a}.DefinableFun LRV (fun z : Fin K → Carrier =>
    SpecialTransformations.Section5.mvPolynomialCode (mulPoly c)
      ((fun z : Fin K → Carrier => (Sum.elim ![z i] Fin.elim0 : Fin 1 ⊕ Fin 0 → Carrier)) z))
  exact hp.comp hinner

/-- The raw tuple with the field coordinates multiplied by `t^{-L}`. -/
def unscaleRaw (L : ℕ) (z : Fin (n + l) → Carrier) : Fin (n + l) → Carrier :=
  fun i => if (i : ℕ) < n then mulCode (tInv L) (z i) else z i

/-- **The scaled set** `{(t^L x, u) | (x, u) ∈ X}` as raw tuples. -/
def scaleRaw (L : ℕ) (X : Set (Fin (n + l) → Carrier)) : Set (Fin (n + l) → Carrier) :=
  {z | (∀ i, sortEval (mixedSorts n l i) (z i)) ∧ unscaleRaw L z ∈ X}

theorem unscaleRaw_mixedRaw (L : ℕ) (p : (Fin n → Ser) × (Fin l → RV)) :
    unscaleRaw L (mixedRaw p) = mixedRaw (unscaleP L p) := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · have h : ((Fin.castAdd l a : Fin (n + l)) : ℕ) < n := a.isLt
    simp only [unscaleRaw, h, ite_true, mixedRaw, Fin.append_left, mulCode_inl, unscaleP]
  · have h : ¬ ((Fin.natAdd n a : Fin (n + l)) : ℕ) < n := by simp
    simp only [unscaleRaw, h, ite_false, mixedRaw, Fin.append_right, unscaleP]

theorem mixedRaw_sorted (p : (Fin n → Ser) × (Fin l → RV)) (i : Fin (n + l)) :
    sortEval (mixedSorts n l i) (mixedRaw p i) := by
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · have hs : mixedSorts n l (Fin.castAdd l a) = .vf := by simp [mixedSorts]
    rw [hs, mixedRaw, Fin.append_left]
    trivial
  · have hs : mixedSorts n l (Fin.natAdd n a) = .rv := by simp [mixedSorts]
    rw [hs, mixedRaw, Fin.append_right]
    exact not_false

theorem mem_mixedSet_scale (L : ℕ) (X : Set (Fin (n + l) → Carrier)) (p : (Fin n → Ser) × (Fin l → RV)) :
    p ∈ mixedSet (scaleRaw L X) ↔ unscaleP L p ∈ mixedSet X := by
  change (_ ∧ unscaleRaw L (mixedRaw p) ∈ X) ↔ mixedRaw (unscaleP L p) ∈ X
  rw [unscaleRaw_mixedRaw]
  exact ⟨fun h => h.2, fun h => ⟨mixedRaw_sorted p, h⟩⟩

theorem mem_mixedSet_scale' (L : ℕ) (X : Set (Fin (n + l) → Carrier)) (p : (Fin n → Ser) × (Fin l → RV)) :
    scaleP L p ∈ mixedSet (scaleRaw L X) ↔ p ∈ mixedSet X := by
  rw [mem_mixedSet_scale, unscaleP_scaleP]

theorem sorted_definable {K : ℕ} (sn : Fin K → SortTag) :
    {c : Carrier | baseCarrier c}.Definable LRV {z : Fin K → Carrier | ∀ i, sortEval (sn i) (z i)} := by
  have h (i : Fin K) := ((definableAt_sort ({c : Carrier | baseCarrier c}) (sn i)).raw_definable).preimage_comp
    (fun _ : Fin 1 => i)
  convert Set.definable_iInter_of_finite h using 1
  ext z
  simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
  rfl

theorem unscaleRaw_definable (L : ℕ) :
    {c : Carrier | baseCarrier c}.DefinableMap LRV (unscaleRaw (n := n) (l := l) L) := by
  intro i
  by_cases h : (i : ℕ) < n
  · simp only [unscaleRaw, h, ite_true]
    exact mulCode_definable (tInv L) (tInv_mem L) i
  · simp only [unscaleRaw, h, ite_false]
    exact Set.DefinableFun.proj LRV

theorem scaleRaw_definableOver (L : ℕ) {X : Set (Fin (n + l) → Carrier)}
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X) :
    DefinableOver {c | baseCarrier c} (mixedSorts n l) (scaleRaw L X) := by
  obtain ⟨hXd, -⟩ := (definableOver_iff_normalized_raw _ _ _).mp hX
  rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical] at hXd
  refine (definableOver_iff_normalized_raw _ _ _).mpr ⟨?_, fun z hz i => hz.1 i⟩
  rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical]
  exact (sorted_definable (mixedSorts n l)).inter (hXd.preimage_map (unscaleRaw_definable L))


/-! ### Extension by zero of diagonal constructible objects -/

section ZeroExt

/-- Extension by zero along `ι`. -/
def extZero {K K' : ℕ} (ι : Fin K → Fin K') (x : Fin K → ℂ) : Fin K' → ℂ := Function.extend ι x 0

theorem extZero_apply {K K' : ℕ} {ι : Fin K → Fin K'} (hι : Function.Injective ι) (x : Fin K → ℂ)
    (a : Fin K) : extZero ι x (ι a) = x a :=
  hι.extend_apply x 0 a

theorem extZero_off {K K' : ℕ} (ι : Fin K → Fin K') (x : Fin K → ℂ) (k : Fin K') (hk : ∀ a, ι a ≠ k) :
    extZero ι x k = 0 := by
  unfold extZero
  rw [Function.extend_apply' x (0 : Fin K' → ℂ) k (fun ⟨a, ha⟩ => hk a ha)]
  rfl

variable (X Y : DiagonalConstructible.Object) (ι : Fin X.arity → Fin Y.arity) (hι : Function.Injective ι)
variable (hd : ∀ y : Fin Y.arity → ℂ, y ∈ Y.domain ↔ y ∘ ι ∈ X.domain ∧ ∀ k, (∀ a, ι a ≠ k) → y k = 0)

/-- The equivalence of domains given by extension by zero. -/
def zeroExtEquiv : X.domain ≃ Y.domain where
  toFun x := ⟨extZero ι x.val, (hd _).mpr ⟨by
      have h : extZero ι x.val ∘ ι = x.val := funext fun a => extZero_apply hι x.val a
      rw [h]
      exact x.property, fun k hk => extZero_off ι x.val k hk⟩⟩
  invFun y := ⟨y.val ∘ ι, ((hd y.val).mp y.property).1⟩
  left_inv x := Subtype.ext (funext fun a => extZero_apply hι x.val a)
  right_inv y := by
    apply Subtype.ext
    funext k
    by_cases hk : ∃ a, ι a = k
    · obtain ⟨a, rfl⟩ := hk
      exact extZero_apply hι _ a
    · push Not at hk
      change extZero ι (y.val ∘ ι) k = y.val k
      rw [extZero_off ι _ k hk, ((hd y.val).mp y.property).2 k hk]

theorem zeroExt_graph :
    framedEquivGraph X.domain Y.domain (zeroExtEquiv X Y ι hι hd) =
      {z | (fun i => z (Fin.castAdd Y.arity i)) ∈ X.domain ∧
        (∀ a, z (Fin.natAdd X.arity (ι a)) = z (Fin.castAdd Y.arity a)) ∧
        ∀ k, (∀ a, ι a ≠ k) → z (Fin.natAdd X.arity k) = 0} := by
  ext z
  simp only [framedEquivGraph, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, hy⟩
    refine ⟨?_, fun a => ?_, fun k hk => ?_⟩
    · rw [hx]
      exact x.property
    · have h1 := congrFun hy (ι a)
      have h2 := congrFun hx a
      change z (Fin.natAdd X.arity (ι a)) = extZero ι x.val (ι a) at h1
      change z (Fin.castAdd Y.arity a) = x.val a at h2
      rw [h1, h2, extZero_apply hι]
    · have h1 := congrFun hy k
      change z (Fin.natAdd X.arity k) = extZero ι x.val k at h1
      rw [h1, extZero_off ι _ k hk]
  · rintro ⟨hx, hι', hz⟩
    refine ⟨⟨fun i => z (Fin.castAdd Y.arity i), hx⟩, rfl, ?_⟩
    funext k
    change z (Fin.natAdd X.arity k) = extZero ι (fun i => z (Fin.castAdd Y.arity i)) k
    by_cases hk : ∃ a, ι a = k
    · obtain ⟨a, rfl⟩ := hk
      rw [extZero_apply hι, hι' a]
    · push Not at hk
      rw [extZero_off ι _ k hk, hz k hk]

/-- **Extension by zero is an isomorphism** when the weights agree up to integers. -/
def zeroExtIso (hw : ∀ (η : CompatibleRoots ℂ) a, compatibleRootCharacter η (Multiplicative.ofAdd (Y.weights (ι a))) =
      compatibleRootCharacter η (Multiplicative.ofAdd (X.weights a))) :
    DiagonalConstructible.Iso X Y where
  equiv := zeroExtEquiv X Y ι hι hd
  graph_definable := by
    rw [zeroExt_graph]
    have h1 := X.definable.preimage_comp (Fin.castAdd Y.arity)
    have h2 := rdef_iInter fun a : Fin X.arity =>
      rdef_coord_eq (Fin.natAdd X.arity (ι a)) (Fin.castAdd Y.arity a)
    have h3 : RDef (⋂ k : Fin Y.arity,
        {z : Fin (X.arity + Y.arity) → ℂ | (∀ a, ι a ≠ k) → z (Fin.natAdd X.arity k) = 0}) := by
      refine rdef_iInter fun k => ?_
      by_cases hk : ∀ a, ι a ≠ k
      · convert rdef_zero (MvPolynomial.X (Fin.natAdd X.arity k) :
          MvPolynomial (Fin (X.arity + Y.arity)) ℂ) using 1
        ext z
        simp [hk]
      · convert rdef_univ (α := Fin (X.arity + Y.arity)) using 1
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact fun h => absurd h hk
    convert h1.inter (h2.inter h3) using 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  graph_invariant := by
    rw [zeroExt_graph]
    intro η z
    have hcast : (fun i => rationalAction (Fin.append X.weights Y.weights) η z (Fin.castAdd Y.arity i)) =
        rationalAction X.weights η (fun i => z (Fin.castAdd Y.arity i)) := by
      funext i
      simp [rationalAction, Fin.append_left]
    simp only [Set.mem_ofPred_eq]
    rw [hcast, X.invariant η]
    refine and_congr Iff.rfl (and_congr (forall_congr' fun a => ?_)
      (forall_congr' fun k => imp_congr_right fun _ => ?_))
    · simp only [rationalAction, Fin.append_left, Fin.append_right, hw]
      constructor
      · intro h
        exact mul_left_cancel₀ (Units.ne_zero _) h
      · intro h
        rw [h]
    · simp only [rationalAction, Fin.append_right]
      constructor
      · intro h
        exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero _)
      · intro h
        rw [h, mul_zero]

end ZeroExt

theorem character_add_nat (η : CompatibleRoots ℂ) (q : ℚ) (L : ℕ) :
    compatibleRootCharacter η (Multiplicative.ofAdd (q + L)) =
      compatibleRootCharacter η (Multiplicative.ofAdd q) := by
  rw [ofAdd_add, map_mul]
  have h1 : compatibleRootCharacter η (Multiplicative.ofAdd (L : ℚ)) = 1 := by
    change compatibleRootValue η (L : ℚ) = 1
    have h := compatibleRootValue_fraction η 1 (L : ℤ)
    have he : ((L : ℤ) : ℚ) / ((1 : ℕ+) : ℕ) = (L : ℚ) := by simp
    rw [he] at h
    rw [h]
    have h1 : η.val 1 = 1 := by
      have := η.property.1 1
      simpa using this
    rw [h1, one_zpow]
  rw [h1, mul_one]

/-! ### Changing the scale -/

variable (m : ℕ+) (b : Fin n → ℕ) (L : ℕ)

/-- The cutoffs `b + mL`. -/
abbrev bL : Fin n → ℕ := fun i => b i + (m : ℕ) * L

theorem ser_ext {x y : Ser} (h : ∀ γ, cf x γ = cf y γ) : x = y :=
  Subtype.ext (by ext γ; exact h γ)

/-- The coefficient of `t^{j/m}` sent to that of `t^{j/m + L}`. -/
def shiftK (k : Idx b) : Idx (bL m b L) :=
  ⟨k.1, ⟨k.2 + (m : ℕ) * L, by have := k.2.isLt; simp only [bL]; omega⟩⟩

theorem shiftK_injective : Function.Injective (shiftK m b L) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [shiftK, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h2⟩ := h
  have h3 := congrArg Fin.val (eq_of_heq h2)
  simp only at h3
  exact congrArg _ (Fin.ext (by omega))

/-- The truncation coordinates of `X` among those of `t^L X`. -/
def shiftIdx : Idx b ⊕ Fin l → Idx (bL m b L) ⊕ Fin l := Sum.map (shiftK m b L) id

theorem shiftIdx_injective : Function.Injective (shiftIdx (l := l) m b L) :=
  Sum.map_injective.mpr ⟨shiftK_injective m b L, Function.injective_id⟩

theorem off_shiftIdx {k : Idx (bL m b L) ⊕ Fin l} (hk : ∀ a, shiftIdx m b L a ≠ k) :
    ∃ i : Fin n, ∃ j : Fin (bL m b L i + 1), (j : ℕ) < (m : ℕ) * L ∧ k = .inl ⟨i, j⟩ := by
  rcases k with ⟨i, j⟩ | j
  · refine ⟨i, j, ?_, rfl⟩
    by_contra hj
    push Not at hj
    apply hk (.inl ⟨i, ⟨j - (m : ℕ) * L, by have := j.isLt; simp only [bL] at this; omega⟩⟩)
    simp only [shiftIdx, Sum.map_inl, shiftK]
    congr 2
    exact Fin.ext (by simp; omega)
  · exact absurd rfl (hk (.inr j))

theorem polyRep_shift (c : Idx (bL m b L) → ℂ)
    (hc : ∀ i (j : Fin (bL m b L i + 1)), (j : ℕ) < (m : ℕ) * L → c ⟨i, j⟩ = 0) (i : Fin n) :
    polyRep m (bL m b L) c i = tPow L * polyRep m b (c ∘ shiftK m b L) i := by
  apply ser_ext
  intro γ
  rw [cf_tPow_mul]
  have hm : (0 : ℚ) < ((m : ℕ) : ℚ) := by exact_mod_cast m.pos
  have hlev : ∀ j : ℕ, lev m (j + (m : ℕ) * L) = lev m j + L := by
    intro j
    rw [lev, lev]
    push_cast
    field_simp
  by_cases hγ : ∃ k : Fin (bL m b L i + 1), γ = lev m k
  · obtain ⟨k, rfl⟩ := hγ
    rw [cf_polyRep_level]
    by_cases hk : (k : ℕ) < (m : ℕ) * L
    · rw [hc i k hk, cf_polyRep_of_not_level]
      intro j hj
      have h1 : lev m k - L < 0 := by
        rw [lev, sub_neg, div_lt_iff₀ hm]
        have hk' : (k : ℕ) < L * (m : ℕ) := by rw [mul_comm]; exact hk
        exact_mod_cast hk'
      rw [hj] at h1
      exact absurd (lev_nonneg m j) (not_le.mpr h1)
    · push Not at hk
      have hj : (k : ℕ) - (m : ℕ) * L < b i + 1 := by have := k.isLt; simp only [bL] at this; omega
      have he : lev m k - L = lev m ((⟨(k : ℕ) - (m : ℕ) * L, hj⟩ : Fin (b i + 1)) : ℕ) := by
        have := hlev ((k : ℕ) - (m : ℕ) * L)
        rw [Nat.sub_add_cancel hk] at this
        simp only
        linarith
      rw [he, cf_polyRep_level]
      simp only [Function.comp_apply, shiftK]
      congr 2
      exact Fin.ext (by simp; omega)
  · push Not at hγ
    rw [cf_polyRep_of_not_level m _ c i γ hγ, cf_polyRep_of_not_level]
    intro j hj
    have hj' : (j : ℕ) + (m : ℕ) * L < bL m b L i + 1 := by have := j.isLt; simp only [bL]; omega
    apply hγ ⟨(j : ℕ) + (m : ℕ) * L, hj'⟩
    rw [hlev, ← hj]
    ring

theorem isRational_tInv {x : Ser} (hx : IsRational m x) : IsRational m (tInv L * x) := by
  intro γ hγ
  have h := cf_tPow_mul L (tInv L * x) (γ + L)
  rw [tPow_mul_tInv, add_sub_cancel_right] at h
  rw [← h] at hγ
  obtain ⟨z, hz⟩ := hx _ hγ
  refine ⟨z - (m : ℕ) * L, ?_⟩
  have hm : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
  push_cast
  rw [sub_div, ← hz]
  field_simp
  ring

/-- Rational points are integral. -/
def RationalIntegral (A : Set ((Fin n → Ser) × (Fin l → RV))) : Prop :=
  ∀ p ∈ A, (∀ i, IsRational m (p.1 i)) → ∀ i, IsIntegral (p.1 i)

variable {X : Set (Fin (n + l) → Carrier)} (q : Fin l → ℤ)

theorem coeffSet_scale (hlow : RationalIntegral m (mixedSet X)) (c : Idx (bL m b L) ⊕ Fin l → ℂ) :
    c ∈ coeffSet m (bL m b L) q (mixedSet (scaleRaw L X)) ↔
      c ∘ shiftIdx m b L ∈ coeffSet m b q (mixedSet X) ∧
        ∀ i (j : Fin (bL m b L i + 1)), (j : ℕ) < (m : ℕ) * L → c (.inl ⟨i, j⟩) = 0 := by
  let y : Fin n → Ser := fun i => tInv L * polyRep m (bL m b L) (fun k => c (.inl k)) i
  let u : Fin l → RV := labelRep m q (fun j => c (.inr j))
  change (polyRep m (bL m b L) (fun k => c (.inl k)), u) ∈ mixedSet (scaleRaw L X) ↔
    (polyRep m b (fun k => c (.inl (shiftK m b L k))), u) ∈ mixedSet X ∧ _
  rw [mem_mixedSet_scale]
  change (y, u) ∈ mixedSet X ↔ _
  have he : ∀ hz : ∀ i (j : Fin (bL m b L i + 1)), (j : ℕ) < (m : ℕ) * L → c (.inl ⟨i, j⟩) = 0,
      y = polyRep m b (fun k => c (.inl (shiftK m b L k))) := by
    intro hz
    funext i
    change tInv L * polyRep m (bL m b L) (fun k => c (.inl k)) i = _
    rw [polyRep_shift m b L _ hz i, tInv_mul_tPow]
    rfl
  constructor
  · intro h
    have hz : ∀ i (j : Fin (bL m b L i + 1)), (j : ℕ) < (m : ℕ) * L → c (.inl ⟨i, j⟩) = 0 := by
      intro i j hj
      have hrat : ∀ i, IsRational m (y i) := fun i => isRational_tInv m L (polyRep_rational m _ _ i)
      have hint := hlow (y, u) h hrat i
      have h1 := cf_tPow_mul L (y i) (lev m j)
      have h2 : tPow L * y i = polyRep m (bL m b L) (fun k => c (.inl k)) i := tPow_mul_tInv L _
      rw [h2, cf_polyRep_level] at h1
      rw [h1]
      apply hint
      have hm : (0 : ℚ) < ((m : ℕ) : ℚ) := by exact_mod_cast m.pos
      rw [lev, sub_neg, div_lt_iff₀ hm]
      have hj' : (j : ℕ) < L * (m : ℕ) := by rw [mul_comm]; exact hj
      exact_mod_cast hj'
    refine ⟨?_, hz⟩
    rw [← he hz]
    exact h
  · rintro ⟨h, hz⟩
    rw [he hz]
    exact h

theorem cf_tInv_mul (x : Ser) (γ : ℚ) : cf (tInv L * x) γ = cf x (γ + L) := by
  have h := cf_tPow_mul L (tInv L * x) (γ + L)
  rw [tPow_mul_tInv, add_sub_cancel_right] at h
  exact h.symm

theorem lev_bL (i : Fin n) : lev m (bL m b L i) = lev m (b i) + L := by
  rw [lev, lev]
  push_cast
  have hm : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
  field_simp

theorem invariant_scale (hA : Invariant m b (mixedSet X)) :
    Invariant m (bL m b L) (mixedSet (scaleRaw L X)) := by
  intro x x' u hx hc
  rw [mem_mixedSet_scale] at hx ⊢
  refine hA _ _ u hx fun i γ hγ => ?_
  change cf (tInv L * x i) γ = cf (tInv L * x' i) γ
  rw [cf_tInv_mul, cf_tInv_mul]
  refine hc i (γ + L) ?_
  rw [lev_bL]
  linarith

theorem covers_scale {Q : Finset (Fin l → ℤ)} (hQ : Covers m Q (mixedSet X))
    (hlow : RationalIntegral m (mixedSet X)) : Covers m Q (mixedSet (scaleRaw L X)) := by
  intro p hp hr hu
  rw [mem_mixedSet_scale] at hp
  have hrat : ∀ i, IsRational m ((unscaleP L p).1 i) := fun i => isRational_tInv m L (hr i).1
  exact hQ (unscaleP L p) hp (fun i => ⟨hrat i, hlow _ hp hrat i⟩) hu

theorem labelsNonzero_scale (hnz : LabelsNonzero (mixedSet X)) : LabelsNonzero (mixedSet (scaleRaw L X)) := by
  intro p hp j
  rw [mem_mixedSet_scale] at hp
  exact hnz _ hp j

theorem sum_bL : ∑ i, bL m b L i = ∑ i, b i + n * ((m : ℕ) * L) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem Linv_add (a c : ℕ) : Linv (a + c) = Linv a * Linv c := pow_add _ _ _

/-- **The truncation class of `t^L X`.** -/
theorem truncClass_scale (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hlow : RationalIntegral m (mixedSet X)) :
    truncClass m (bL m b L) q (scaleRaw_definableOver L hX) = truncClass m b q hX * Linv (n * ((m : ℕ) * L)) := by
  let ε := Fintype.equivFin (Idx b ⊕ Fin l)
  let ε' := Fintype.equivFin (Idx (bL m b L) ⊕ Fin l)
  let X0 := truncObject m b q hX ε
  let Y0 := truncObject m (bL m b L) q (scaleRaw_definableOver L hX) ε'
  let ι0 : Fin X0.arity → Fin Y0.arity := fun a => ε' (shiftIdx m b L (ε.symm a))
  have hι0 : Function.Injective ι0 := by
    intro a a' h
    have h1 := shiftIdx_injective m b L (ε'.injective h)
    exact ε.symm.injective h1
  have hd0 : ∀ y : Fin Y0.arity → ℂ, y ∈ Y0.domain ↔ y ∘ ι0 ∈ X0.domain ∧
      ∀ k, (∀ a, ι0 a ≠ k) → y k = 0 := by
    intro y
    have hY : Y0.domain = {x | x ∘ ε' ∈ coeffSet m (bL m b L) q (mixedSet (scaleRaw L X))} :=
      truncObject_domain m (bL m b L) q (scaleRaw_definableOver L hX) ε'
    have hX0 : X0.domain = {x | x ∘ ε ∈ coeffSet m b q (mixedSet X)} := truncObject_domain m b q hX ε
    rw [hY, hX0]
    change y ∘ ε' ∈ coeffSet m (bL m b L) q (mixedSet (scaleRaw L X)) ↔
      (y ∘ ι0) ∘ ε ∈ coeffSet m b q (mixedSet X) ∧ _
    rw [coeffSet_scale m b L q hlow]
    have hcomp : (y ∘ ι0) ∘ ε = (y ∘ ε') ∘ shiftIdx m b L := by
      funext a
      simp [ι0]
    rw [hcomp]
    refine and_congr Iff.rfl ⟨fun hz k hk => ?_, fun hz i j hj => ?_⟩
    · have hk' : ∀ a, shiftIdx m b L a ≠ ε'.symm k := by
        intro a ha
        apply hk (ε a)
        simp [ι0, ha]
      obtain ⟨i, j, hj, hkj⟩ := off_shiftIdx m b L hk'
      have := hz i j hj
      rw [← hkj] at this
      simpa using this
    · refine hz (ε' (.inl ⟨i, j⟩)) fun a ha => ?_
      have h1 := ε'.injective ha
      rcases hs : ε.symm a with ⟨i', j'⟩ | j'
      · rw [hs] at h1
        simp only [shiftIdx, Sum.map_inl, shiftK, Sum.inl.injEq, Sigma.mk.inj_iff] at h1
        obtain ⟨rfl, h2⟩ := h1
        have h3 := congrArg Fin.val (eq_of_heq h2)
        simp only at h3
        omega
      · rw [hs] at h1
        simp [shiftIdx] at h1
  have hw0 : ∀ (η : CompatibleRoots ℂ) a, compatibleRootCharacter η (Multiplicative.ofAdd (Y0.weights (ι0 a))) =
      compatibleRootCharacter η (Multiplicative.ofAdd (X0.weights a)) := by
    intro η a
    change compatibleRootCharacter η (Multiplicative.ofAdd (stdWt m (bL m b L) q (ε'.symm (ι0 a)))) =
      compatibleRootCharacter η (Multiplicative.ofAdd (stdWt m b q (ε.symm a)))
    simp only [ι0, Equiv.symm_apply_apply]
    rcases ε.symm a with ⟨i, j⟩ | j
    · simp only [shiftIdx, Sum.map_inl, shiftK, stdWt, Sum.elim_inl]
      have he : lev m ((j : ℕ) + (m : ℕ) * L) = lev m j + L := by
        rw [lev, lev]
        push_cast
        have hm : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
        field_simp
      rw [he, character_add_nat]
    · rfl
  have hcls : dcClass Y0 = dcClass X0 := (dcClass_iso (zeroExtIso X0 Y0 ι0 hι0 hd0 hw0)).symm
  change algebraMap _ Rloc (dcClass Y0) * Linv (∑ i, bL m b L i) =
    (algebraMap _ Rloc (dcClass X0) * Linv (∑ i, b i)) * Linv (n * ((m : ℕ) * L))
  rw [hcls, sum_bL, Linv_add, mul_assoc]

/-- **The normalized truncation class of `t^L X`**: `[(t^L X)[m; β + L]] 𝕃^{-m Σ(β + L)} =
[X[m;β]] 𝕃^{-mΣβ} 𝕃^{-mnL}`. -/
theorem fullClass_scale (Q : Finset (Fin l → ℤ)) (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hA : Invariant m b (mixedSet X)) (hQ : Covers m Q (mixedSet X)) (hnz : LabelsNonzero (mixedSet X))
    (hlow : RationalIntegral m (mixedSet X)) :
    fullClass m (bL m b L) Q (scaleRaw_definableOver L hX) (invariant_scale m b L hA)
        (covers_scale m L hQ hlow) =
      fullClass m b Q hX hA hQ * Linv (n * ((m : ℕ) * L)) := by
  rw [fullClass_eq_sum m _ Q _ _ _ (labelsNonzero_scale L hnz), fullClass_eq_sum m b Q hX hA hQ hnz,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => truncClass_scale m b L q hX hlow

end DiamondIntegral.Section8.Truncation
