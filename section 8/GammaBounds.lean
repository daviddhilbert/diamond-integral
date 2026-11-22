import «section 8».GammaHalfspaces

/-! Definable points and bounds in the value group.

Over a base `⟨R, ∅⟩` whose substructure values are rational powers of a definable `π > 1`:

* `definable_point_rational`: every definable point of `Γ` is a rational power `qpow π q`;
* `proj_definable`: coordinate projections of definable sets are definable;
* `exists_pow_bound`: a definable subset of `Γⁿ` that is bounded by some `β ∈ Γ` (the notion of
  the library, `DomainBounded`) is bounded by a power `π ^ N`.

The second statement is needed because `β` may be infinitely large compared with `π`; for a
definable set the bound can be taken rational. In one variable a definable set is a union of sign
classes of affine functions `c y + d`; beyond the largest root all points have the same signature,
so a set that reaches beyond `π ^ N` contains points beyond `β`. -/

set_option autoImplicit false

noncomputable section

namespace DiamondIntegral.Section8.GammaCells

open Prism
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 GammaOrderLogic
open DiamondIntegral.Section2.GammaStable

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

local notation "Γ" => Values.Gamma (M := M)

/-- A definable point of `Γ` is a rational power of `π`. -/
theorem definable_point_rational (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) (R : Set M) (hr : Cardinal.mk R < κ)
    {π : Γ} (hπ1 : 1 < π)
    (hΔ : ∀ δ ∈ substructureValues (Substructure.closure LRV R), ∃ q : ℚ, δ = qpow π q)
    {δ : Γ} (hδ : GammaDefinableClosureAtBase ⟨R, ∅⟩ δ) : ∃ q : ℚ, δ = qpow π q := by
  have hX : GammaDefinable ⟨R, ∅⟩ {z : Fin 1 → Γ | z 0 ∈ ({δ} : Set Γ)} :=
    (unary_definable_iff _ _).mpr hδ
  obtain ⟨G, S, hS, hXS⟩ := saturated_of_halfspaceBoolean hΔ
    (gamma_stably_embedded hc hκ hs hh R hr _ (codeSet_definable hc R hX))
  have he := pos_ι_of_one_lt hπ1
  have hz : (fun _ : Fin 1 => δ) ∈ real S := by
    rw [← hXS]; rfl
  obtain ⟨x, hx⟩ := exists_rat_signs he 1 G (fun i => ι ((fun _ : Fin 1 => δ) (Fin.rev i)))
  have hxS : (fun i => x i • ι π) ∈ S := by
    refine (hS _ _ fun g hg => ?_).mp hz
    rw [AffFun.evalV_emb, sign_smul_pos he, ← hx g hg]
  have hxX : (fun i => qpow π (x (Fin.rev i))) ∈ real S := by
    change (fun j => ι (qpow π (x (Fin.rev (Fin.rev j))))) ∈ S
    simpa only [ι_qpow, Fin.rev_rev] using hxS
  rw [← hXS] at hxX
  exact ⟨x 0, (show qpow π (x (Fin.rev 0)) = δ from hxX).symm⟩

/-- Coordinate projections of definable sets are definable. -/
theorem proj_definable (B : Base (M := M)) {n : ℕ} (X : Set (Fin n → Γ)) (hX : GammaDefinable B X)
    (i : Fin n) : GammaDefinable B {y : Fin 1 → Γ | ∃ z ∈ X, z i = y 0} := by
  have h : DefinableOverBase B (fun _ : Fin 1 => .rv) ((fun w => w ∘ (fun _ : Fin 1 => i)) ''
      {z : Fin n → M | Proper z ∧ (fun j => codeValue (M := M) (z j)) ∈ X}) :=
    DefinableOverBase.image_real hX (fun _ : Fin 1 => i)
  unfold GammaDefinable
  convert h using 1
  refine Set.ext fun u => ?_
  change (Proper u ∧ ∃ z ∈ X, z i = codeValue (M := M) (u 0)) ↔
    ∃ w, (Proper w ∧ (fun j => codeValue (M := M) (w j)) ∈ X) ∧ w ∘ (fun _ : Fin 1 => i) = u
  constructor
  · rintro ⟨hu, z, hz, hzi⟩
    choose t ht htz using fun j => EndpointLogic.codeValue_surjective (z j)
    refine ⟨Function.update t i (u 0), ⟨fun j => ?_, ?_⟩, ?_⟩
    · by_cases hj : j = i
      · subst hj; rw [Function.update_self]; exact hu 0
      · rw [Function.update_of_ne hj]; exact ht j
    · convert hz using 1
      funext j
      by_cases hj : j = i
      · subst hj; rw [Function.update_self, hzi]
      · rw [Function.update_of_ne hj, htz]
    · funext j
      rw [Subsingleton.elim j 0]
      simp
  · rintro ⟨w, ⟨hw, hwX⟩, rfl⟩
    exact ⟨fun _ => hw i, _, hwX, rfl⟩

/-- In one variable, all points far out have the same signature. -/
theorem sign_far (e : Hull Γ) (he : 0 < e) (g : AffFun 1) (N : ℚ)
    (hN : |g.const / g.coeff 0| < N) {z : Hull Γ} :
    (N • e < z → SignType.sign (g.evalV e (fun _ => z)) =
        if g.coeff 0 = 0 then SignType.sign g.const else SignType.sign (g.coeff 0)) ∧
    (z < (-N) • e → SignType.sign (g.evalV e (fun _ => z)) =
        if g.coeff 0 = 0 then SignType.sign g.const else -SignType.sign (g.coeff 0)) := by
  have hval : g.evalV e (fun _ => z) = g.coeff 0 • z + g.const • e := by
    simp [AffFun.evalV]
  by_cases hc : g.coeff 0 = 0
  · simp only [hc, ite_true, hval, zero_smul, zero_add, sign_smul_pos he, implies_true, and_self]
  · simp only [hc, ite_false]
    set r : ℚ := g.const / g.coeff 0 with hr
    have hcr : g.coeff 0 * r = g.const := by rw [hr]; field_simp
    have hroot : g.coeff 0 • z + g.const • e = g.coeff 0 • (z - (-r) • e) := by
      rw [smul_sub, smul_smul, mul_neg, ← hcr, neg_smul, sub_neg_eq_add]
    rw [hval, hroot, sign_smul]
    have h1 : r < N := lt_of_le_of_lt (le_abs_self r) hN
    have h2 : -r < N := lt_of_le_of_lt (neg_le_abs r) hN
    constructor
    · intro hz
      have : (-r) • e < z := lt_of_le_of_lt ((smul_le_smul_iff_of_pos_right he).mpr h2.le) hz
      rw [sign_pos (sub_pos.mpr this), mul_one]
    · intro hz
      have : z < (-r) • e :=
        lt_of_lt_of_le hz ((smul_le_smul_iff_of_pos_right he).mpr (by linarith))
      rw [sign_neg (sub_neg.mpr this), mul_neg_one]

/-- A rational bound beyond the roots of finitely many affine functions of one variable. -/
theorem exists_far_bound (G : List (AffFun 1)) :
    ∃ N : ℕ, ∀ g ∈ G, |g.const / g.coeff 0| < N := by
  refine ⟨⌈(G.map fun g => |g.const / g.coeff 0|).sum⌉₊ + 1, fun g hg => ?_⟩
  have h1 : |g.const / g.coeff 0| ≤ (G.map fun g => |g.const / g.coeff 0|).sum :=
    List.single_le_sum (fun _ hx => by
      obtain ⟨g', -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _) _
      (List.mem_map.mpr ⟨g, hg, rfl⟩)
  have h2 := Nat.le_ceil ((G.map fun g => |g.const / g.coeff 0|).sum)
  push_cast
  linarith

/-- A definable subset of `Γ` bounded by some `β` is bounded by a power of `π`. -/
theorem exists_pow_bound_one (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) (R : Set M) (hr : Cardinal.mk R < κ)
    {π : Γ} (hπ1 : 1 < π)
    (hΔ : ∀ δ ∈ substructureValues (Substructure.closure LRV R), ∃ q : ℚ, δ = qpow π q)
    (Y : Set (Fin 1 → Γ)) (hY : GammaDefinable ⟨R, ∅⟩ Y) (β : Γ)
    (hβ : ∀ y ∈ Y, β⁻¹ ≤ y 0 ∧ y 0 ≤ β) :
    ∃ N : ℕ, ∀ y ∈ Y, π ^ (-(N : ℤ)) ≤ y 0 ∧ y 0 ≤ π ^ (N : ℤ) := by
  obtain ⟨G, S, hS, rfl⟩ := saturated_of_halfspaceBoolean hΔ
    (gamma_stably_embedded hc hκ hs hh R hr Y (codeSet_definable hc R hY))
  have he := pos_ι_of_one_lt hπ1
  obtain ⟨N, hN⟩ := exists_far_bound G
  -- Points of `Γ` beyond `π ^ N`, resp. below `π ^ (-N)`, have a common signature.
  have hfar : ∀ γ δ : Γ, (π ^ (N : ℤ) < γ ∧ π ^ (N : ℤ) < δ) ∨
      (γ < π ^ (-(N : ℤ)) ∧ δ < π ^ (-(N : ℤ))) →
      ((fun _ : Fin 1 => γ) ∈ real S ↔ (fun _ : Fin 1 => δ) ∈ real S) := by
    intro γ δ h
    refine hS _ _ fun g hg => ?_
    have hg' := hN g hg
    have hrev : ∀ x : Γ, (fun i : Fin 1 => ι ((fun _ : Fin 1 => x) (Fin.rev i))) = fun _ => ι x :=
      fun _ => rfl
    rw [hrev, hrev]
    have hι : ∀ x : Γ, π ^ (N : ℤ) < x → ((N : ℚ) • ι π < ι x) := fun x hx => by
      have h := ι_lt_iff.mpr hx
      rw [ι_zpow_rat, Int.cast_natCast] at h
      exact h
    have hι' : ∀ x : Γ, x < π ^ (-(N : ℤ)) → ι x < (-(N : ℚ)) • ι π := fun x hx => by
      have h := ι_lt_iff.mpr hx
      rw [ι_zpow_rat, Int.cast_neg, Int.cast_natCast] at h
      exact h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [(sign_far _ he g N hg').1 (hι γ h1), (sign_far _ he g N hg').1 (hι δ h2)]
    · rw [(sign_far _ he g N hg').2 (hι' γ h1), (sign_far _ he g N hg').2 (hι' δ h2)]
  refine ⟨N, fun y hy => ⟨?_, ?_⟩⟩
  · by_contra hlt
    push Not at hlt
    have hy' : y = fun _ => y 0 := funext fun i => by rw [Subsingleton.elim i 0]
    let δ : Γ := min β⁻¹ (π ^ (-(N : ℤ))) * π⁻¹
    have hδlt : δ < min β⁻¹ (π ^ (-(N : ℤ))) := mul_lt_of_lt_one_right' _ (inv_lt_one'.mpr hπ1)
    have hδ := (hfar (y 0) δ (Or.inr ⟨hlt, lt_of_lt_of_le hδlt (min_le_right _ _)⟩)).mp
      (by rw [← hy']; exact hy)
    have := (hβ _ hδ).1
    exact absurd (lt_of_lt_of_le hδlt (min_le_left _ _)) (not_lt.mpr this)
  · by_contra hlt
    push Not at hlt
    have hy' : y = fun _ => y 0 := funext fun i => by rw [Subsingleton.elim i 0]
    let δ : Γ := max β (π ^ (N : ℤ)) * π
    have hδgt : max β (π ^ (N : ℤ)) < δ := lt_mul_of_one_lt_right' _ hπ1
    have hδ := (hfar (y 0) δ (Or.inl ⟨hlt, lt_of_le_of_lt (le_max_right _ _) hδgt⟩)).mp
      (by rw [← hy']; exact hy)
    have := (hβ _ hδ).2
    exact absurd (lt_of_le_of_lt (le_max_left _ _) hδgt) (not_lt.mpr this)

/-- **Rational bounds.** A definable subset of `Γⁿ` bounded by some `β` is bounded by a power
of `π`. -/
theorem exists_pow_bound (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) (R : Set M) (hr : Cardinal.mk R < κ)
    {π : Γ} (hπ1 : 1 < π)
    (hΔ : ∀ δ ∈ substructureValues (Substructure.closure LRV R), ∃ q : ℚ, δ = qpow π q)
    {n : ℕ} (X : Set (Fin n → Γ)) (hX : GammaDefinable ⟨R, ∅⟩ X) (β : Γ)
    (hβ : ∀ z ∈ X, ∀ i, β⁻¹ ≤ z i ∧ z i ≤ β) :
    ∃ N : ℕ, ∀ z ∈ X, ∀ i, π ^ (-(N : ℤ)) ≤ z i ∧ z i ≤ π ^ (N : ℤ) := by
  have hi : ∀ i : Fin n, ∃ N : ℕ, ∀ z ∈ X, π ^ (-(N : ℤ)) ≤ z i ∧ z i ≤ π ^ (N : ℤ) := by
    intro i
    obtain ⟨N, hN⟩ := exists_pow_bound_one hc hκ hs hh R hr hπ1 hΔ _
      (proj_definable _ X hX i) β (by rintro y ⟨z, hz, hzy⟩; rw [← hzy]; exact hβ z hz i)
    exact ⟨N, fun z hz => hN (fun _ => z i) ⟨z, hz, rfl⟩⟩
  choose N hN using hi
  refine ⟨Finset.univ.sup N, fun z hz i => ?_⟩
  have hle : N i ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨h1, h2⟩ := hN i z hz
  constructor
  · refine le_trans ?_ h1
    exact (zpow_right_strictMono hπ1).monotone (by push_cast; omega)
  · refine le_trans h2 ?_
    exact (zpow_right_strictMono hπ1).monotone (by push_cast; omega)

end DiamondIntegral.Section8.GammaCells
