import «section 8».MapLattice
import «section 8».GammaHalfspaces
import «section 8».ZetaRES

/-! # Remark 8.7: an object outside the images of Hrushovski–Kazhdan, Proposition 10.10(2)

Hrushovski and Loeser's `vol RV[n]` has the objects `(X, f)` of `RV[n]`; a morphism
`(X, f) → (X', f')` is a definable bijection `h` with `w (f x) = w (f' (h x))`, where `w` is the sum
of the values of the coordinates. The classes in the images of the maps (8.1.4), (8.1.6) and
(8.1.7) of Hrushovski–Loeser, and of the map of Hrushovski–Kazhdan, Proposition 10.10(2), are
classes of finite disjoint unions of products `W × Δ♯`. In degree one there are two kinds:
`W ∈ RES[1]` with `l = 0`, on which the weight takes finitely many values, and `W` finite with
`Δ ⊆ Γ` definable, where the point `(p, y)` has weight `vrv y`.

The paper's object is `X = {u ∈ RV : 0 < vrv u < 1}` with `f u = u²`, so `w (f u) = 2 vrv u`. Here
`Γ` is written multiplicatively, with `π = vrv t > 1`, so `X = {u : 1 < vrv u < π}` and the weight
of `u` is `vrv u ^ 2`.

`remark_8_7`: let `Y ⊆ RV^{n+1}` be definable with a weight `w_Y`, covered by a part `Y₁` on which
`w_Y` takes finitely many values and by products `W_j × Δ_j♯` (`secondKind`: `W_j ⊆ RVⁿ` finite and
definable, `Δ_j ⊆ Γ` definable, the last coordinate in `Δ_j♯`, weight its value) that lie in `Y`.
There is no bijection `h : X → Y` with definable inverse `g` such that `w_Y (h u) = vrv u ^ 2`.
This is more general than the paper's claim, which has `Y₁` a union of `RES[1]` objects and the
pieces disjoint.

Proof (as in the paper, with values in place of rational points). Choose `m` such that the
coordinates of the points of the finite sets `W_j` have values in `π^{m⁻¹ℤ}`, `π^{2/m}` is not a
weight on `Y₁`, and `2/m` lies below the point after which each `Δ_j` is constant near `1`
(`germ`, from the description of definable subsets of `Γ` as unions of sign classes). A point
`u ∈ X` of value `π^{1/m}` has weight `π^{2/m}`, so `h u` lies in some `W_j × Δ_j♯` with
`π^{2/m} ∈ Δ_j`; hence `π^{1/m} ∈ Δ_j`, and `(p, u)` lies in `W_j × Δ_j♯ ⊆ Y` for the first
coordinates `p` of `h u`. All its coordinates have values in `π^{m⁻¹ℤ}`, so the value of
`g (p, u)` is in `π^{m⁻¹ℤ}` (`map_lattice`: definable maps preserve the lattice). But its square is
the weight `π^{1/m}` of `(p, u)`, which has no square root in `π^{m⁻¹ℤ}`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Remark87

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts RVVolumeMaps
open DiamondIntegral.Section4.GammaOrderLogic
open DiamondIntegral.Section8.GammaCells DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.Hm
open DiamondIntegral.Section8.Prism DiamondIntegral.Section2.GammaStable
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open FiniteTupleBlocks DiamondIntegral.Section8.ValueMaps GammaDefinableMaps GammaRVChartPresentation

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

/-- `X = {u ∈ RV : 0 < vrv u < 1}`, that is `1 < vrv u < π` in multiplicative notation. -/
def X : Set (Fin 1 → P.N) :=
  {x | NonzeroRV (x 0) ∧ 1 < codeValue (x 0) ∧ codeValue (x 0) < π}

/-- A product `W × Δ♯ ⊆ RVⁿ × RV` of the second kind. -/
def secondKind {n : ℕ} (W : Set (Fin n → P.N)) (Δ : Set Γ) : Set (Fin (n + 1) → P.N) :=
  {y | Fin.init y ∈ W ∧ NonzeroRV (y (Fin.last n)) ∧ codeValue (y (Fin.last n)) ∈ Δ}

/-! ### Definable subsets of `Γ` are constant just above `1` -/

theorem sign_add_of_abs_lt {x c : ℚ} (h : |x| < |c|) : SignType.sign (x + c) = SignType.sign c := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · rw [abs_of_neg hc] at h
    have : x + c < 0 := by linarith [le_abs_self x]
    rw [sign_neg this, sign_neg hc]
  · rw [hc, abs_zero] at h
    exact absurd h (not_lt.mpr (abs_nonneg x))
  · rw [abs_of_pos hc] at h
    have : 0 < x + c := by linarith [neg_abs_le x]
    rw [sign_pos this, sign_pos hc]

theorem sign_smul_pos {x : ℚ} {v : Hull Γ} (hv : 0 < v) : SignType.sign (x • v) = SignType.sign x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [sign_neg hx, sign_neg (smul_neg_of_neg_of_pos hx hv)]
  · simp
  · rw [sign_pos hx, sign_pos (smul_pos hx hv)]

/-- The sign of `a r + c` for small positive `r`. -/
theorem sign_small {a c r : ℚ} {N : ℕ} (hN : (if c = 0 then 0 else ⌈|a| / |c|⌉₊) < N)
    (hr : 0 < r) (hrN : r * N < 1) :
    SignType.sign (a * r + c) = if c = 0 then SignType.sign a else SignType.sign c := by
  split_ifs at hN ⊢ with hc
  · rw [hc, add_zero, sign_mul, sign_pos hr, mul_one]
  · apply sign_add_of_abs_lt
    have hc' : 0 < |c| := abs_pos.mpr hc
    have hN' : |a| / |c| < N := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)
    have hNpos : (0 : ℚ) < N := lt_of_le_of_lt (div_nonneg (abs_nonneg a) hc'.le) hN'
    rw [abs_mul, abs_of_pos hr]
    have h1 : |a| < N * |c| := (div_lt_iff₀ hc').mp hN'
    have h2 : r < 1 / N := by rw [lt_div_iff₀ hNpos]; exact hrN
    calc |a| * r ≤ |a| * (1 / N) := mul_le_mul_of_nonneg_left h2.le (abs_nonneg a)
      _ = |a| / N := by ring
      _ < |c| := by rw [div_lt_iff₀ hNpos]; linarith

/-- **Germ at `1`.** A subset of `Γ` definable over the base is, just above `1`, either all of
`(1, π^{1/N})` or disjoint from it. -/
theorem germ (Δ : Set Γ) (hΔ : GammaDefinable (base P) {z : Fin 1 → Γ | z 0 ∈ Δ}) :
    ∃ N : ℕ, 0 < N ∧ ∀ q q' : ℚ, 0 < q → q * N < 1 → 0 < q' → q' * N < 1 →
      (qpow π q ∈ Δ ↔ qpow π q' ∈ Δ) := by
  obtain ⟨G, S, hS, hXS⟩ := saturated_of_halfspaceBoolean (substructureValues_rational P)
    (gamma_stably_embedded P.hc P.G.uncountable P.G.saturated P.G.homogeneous
      (P.G.real : Set P.N) P.G.small_real _ (codeSet_definable P.hc _ hΔ))
  have hmem : ∀ q : ℚ, qpow π q ∈ Δ ↔ (fun _ : Fin 1 => q • ι π) ∈ S := by
    intro q
    have h := Set.ext_iff.mp hXS (fun _ => qpow π q)
    simp only [Set.mem_ofPred_eq] at h
    rw [h]
    change (fun i => ι (qpow π q)) ∈ S ↔ _
    simp only [ι_qpow]
  let bound : AffFun 1 → ℕ := fun g => if g.const = 0 then 0 else ⌈|g.coeff 0| / |g.const|⌉₊
  refine ⟨1 + (G.map bound).sum, by omega, fun q q' hq hqN hq' hq'N => ?_⟩
  rw [hmem, hmem]
  apply hS
  intro g hg
  have hb : bound g < 1 + (G.map bound).sum :=
    Nat.lt_one_add_iff.mpr (List.le_sum_of_mem (List.mem_map_of_mem hg))
  have hev : ∀ r : ℚ, g.evalV (ι π) (fun _ : Fin 1 => r • ι π) = (g.coeff 0 * r + g.const) • ι π := by
    intro r
    simp only [AffFun.evalV, Fin.sum_univ_one, smul_smul, ← add_smul]
  have he : 0 < ι π := pos_ι_of_one_lt (one_lt_uniformizerValue P)
  rw [hev, hev, sign_smul_pos P he, sign_smul_pos P he, sign_small hb hq hqN, sign_small hb hq' hq'N]

/-! ### The counterexample -/

/-- Values of the coordinates of the points of a finite definable set are rational. -/
theorem finite_level {n : ℕ} (W : Set (Fin n → P.N)) (hW : W.Finite)
    (hWd : DefinableOverBase (base P) (fun _ : Fin n => .rv) W) :
    ∃ N : ℕ, 0 < N ∧ ∀ p ∈ W, ∀ i, InLattice π N (codeValue (p i)) := by
  have hdef : ∀ p ∈ W, ∀ i, ∃ q : ℚ, codeValue (p i) = qpow π q := by
    intro p hp i
    have hfin : ((fun u : Fin n → P.N => codeValue (u i)) '' W).Finite := hW.image _
    refine definable_point_rational P ?_
    refine gamma_finset_element_definable_base (base P) hfin.toFinset ?_ _
      (hfin.mem_toFinset.mpr ⟨p, hp, rfl⟩)
    rw [hfin.coe_toFinset]
    exact image_definable (base P) (coord_volume_definable (base P) hWd i)
  choose! q hq using hdef
  let T : Finset ((Fin n → P.N) × Fin n) := hW.toFinset ×ˢ Finset.univ
  refine ⟨∏ x ∈ T, (q x.1 x.2).den, Finset.prod_pos fun x _ => (q x.1 x.2).den_pos, ?_⟩
  intro p hp i
  rw [hq p hp i]
  have hmem : (p, i) ∈ T := Finset.mem_product.mpr ⟨hW.mem_toFinset.mpr hp, Finset.mem_univ i⟩
  exact inLattice_qpow_of_dvd P _
    (Finset.dvd_prod_of_mem (fun x : (Fin n → P.N) × Fin n => (q x.1 x.2).den) hmem)

/-- Every value is the value of a nonzero element of `RV`. -/
theorem exists_rv_of_value (δ : Γ) : ∃ u : P.N, NonzeroRV u ∧ codeValue u = δ := by
  obtain ⟨t, ht⟩ := Values.vrv_surjective δ.val
  have hne : Values.vrv t ≠ Values.infinity := by rw [ht]; exact δ.property
  refine ⟨t.val, ⟨t.property, fun h => hne ((Values.vrv_eq_infinity_iff t).mpr h)⟩, ?_⟩
  rw [← RVMeasuredBounds.finiteValue_vrv t, ht]
  simp only [RVMeasuredBounds.finiteValue, δ.property, ne_eq, not_false_eq_true, ↓reduceDIte]
  rfl

/-- **Remark 8.7.** No bijection with definable inverse, preserving the weights, between
`X = {u : 0 < vrv u < 1}` with the weight `2 vrv u` of `f u = u²` and a set covered by a part with
finitely many weights and products `W × Δ♯` of the second kind. -/
theorem remark_8_7 {n b : ℕ} (Y : Set (Fin (n + 1) → P.N))
    (hY : DefinableOverBase (base P) (fun _ : Fin (n + 1) => .rv) Y)
    (wY : (Fin (n + 1) → P.N) → Γ) (Y₁ : Set (Fin (n + 1) → P.N)) (S : Finset Γ)
    (hY₁ : ∀ y ∈ Y₁, wY y ∈ S)
    (W : Fin b → Set (Fin n → P.N)) (hW : ∀ j, (W j).Finite)
    (hWd : ∀ j, DefinableOverBase (base P) (fun _ : Fin n => .rv) (W j))
    (Δ : Fin b → Set Γ) (hΔ : ∀ j, GammaDefinable (base P) {z : Fin 1 → Γ | z 0 ∈ Δ j})
    (hcover : Y ⊆ Y₁ ∪ ⋃ j, secondKind P (W j) (Δ j))
    (hprod : ∀ j, secondKind P (W j) (Δ j) ⊆ Y)
    (hwprod : ∀ j, ∀ y ∈ secondKind P (W j) (Δ j), wY y = codeValue (y (Fin.last n)))
    (h : (Fin 1 → P.N) → (Fin (n + 1) → P.N)) (g : (Fin (n + 1) → P.N) → (Fin 1 → P.N))
    (hg : DefinableOverBase (base P) (fun _ : Fin (1 + (n + 1)) => .rv) (graphOn Y g))
    (hhY : ∀ x ∈ X P, h x ∈ Y) (hhg : ∀ y ∈ Y, h (g y) = y) (hgX : ∀ y ∈ Y, g y ∈ X P)
    (hw : ∀ x ∈ X P, wY (h x) = codeValue (x 0) ^ 2) : False := by
  have hπ := one_lt_uniformizerValue P
  have he : 0 < ι π := pos_ι_of_one_lt hπ
  -- the levels of the finite sets and the germs of the `Δ j`
  choose N₀ hN₀pos hN₀ using fun j => finite_level P (W j) (hW j) (hWd j)
  choose Ng hNgpos hNg using fun j => germ P (Δ j) (hΔ j)
  let L : ℕ := (∏ j, N₀ j) * (2 * ∏ j, Ng j + 1)
  have hLpos : 0 < L := Nat.mul_pos (Finset.prod_pos fun j _ => hN₀pos j) (by omega)
  -- `π^{2/m}` is not a weight on `Y₁`, for some multiple `m` of `L`
  have hpig : ∃ k ∈ Finset.range (S.card + 1), qpow π (2 / ((L * (k + 1) : ℕ) : ℚ)) ∉ S := by
    by_contra hall
    push Not at hall
    have hinj : Set.InjOn (fun k : ℕ => qpow π (2 / ((L * (k + 1) : ℕ) : ℚ)))
        (Finset.range (S.card + 1) : Set ℕ) := by
      intro a _ c _ hac
      have hq := qpow_injective hπ hac
      have hL : (0 : ℚ) < L := by exact_mod_cast hLpos
      push_cast at hq
      field_simp at hq
      have : (a : ℚ) = c := by linarith
      exact_mod_cast this
    have := Finset.card_le_card_of_injOn _ (fun k hk => hall k hk) hinj
    simp at this
  obtain ⟨k, -, hk⟩ := hpig
  set m : ℕ := L * (k + 1) with hm
  have hmpos : 0 < m := Nat.mul_pos hLpos (Nat.succ_pos k)
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hmpos
  have hbig : 2 * ∏ i, Ng i + 1 ≤ m := by
    calc 2 * ∏ i, Ng i + 1 ≤ L := Nat.le_mul_of_pos_left _ (Finset.prod_pos fun j _ => hN₀pos j)
      _ ≤ m := Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
  have hNgprod : 0 < ∏ i, Ng i := Finset.prod_pos fun i _ => hNgpos i
  have hm1 : 1 < m := by omega
  have hNgm : ∀ j, 2 * Ng j < m := by
    intro j
    have h1 : Ng j ∣ ∏ i, Ng i := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have h2 : Ng j ≤ ∏ i, Ng i := Nat.le_of_dvd hNgprod h1
    omega
  have hN₀m : ∀ j, N₀ j ∣ m :=
    fun j => Dvd.dvd.mul_right (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _) _
  -- the point of value `π^{1/m}`
  obtain ⟨u, hu0, hucode⟩ := exists_rv_of_value P (qpow π (1 / m))
  let x₀ : Fin 1 → P.N := fun _ => u
  have hι : ∀ q : ℚ, ι (qpow π q) = q • ι π := ι_qpow π
  have hx₀ : x₀ ∈ X P := by
    refine ⟨hu0, ?_, ?_⟩
    · change 1 < codeValue u
      rw [hucode, ← ι_lt_iff, hι, ι_one]
      exact smul_pos (by positivity) he
    · change codeValue u < π
      rw [hucode, ← ι_lt_iff, hι]
      have : (1 / (m : ℚ)) < 1 := by
        rw [div_lt_one hmQ]; exact_mod_cast hm1
      calc (1 / (m : ℚ)) • ι π < (1 : ℚ) • ι π := smul_lt_smul_of_pos_right this he
        _ = ι π := one_smul _ _
  have hsq : qpow π (1 / m) ^ 2 = qpow π (2 / m) := by
    apply ι_injective
    rw [ι_npow, hι, hι, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
    congr 1; push_cast; ring
  have hw₀ : wY (h x₀) = qpow π (2 / m) := by rw [hw x₀ hx₀]; change codeValue u ^ 2 = _; rw [hucode, hsq]
  rcases hcover (hhY x₀ hx₀) with hy₁ | hy₂
  · exact hk (by have := hY₁ _ hy₁; rwa [hw₀] at this)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy₂
  have hΔ2 : qpow π (2 / m) ∈ Δ j := by rw [← hw₀, hwprod j _ hj]; exact hj.2.2
  have hNgQ : (2 : ℚ) * Ng j < m := by exact_mod_cast hNgm j
  have hΔ1 : qpow π (1 / m) ∈ Δ j := by
    refine (hNg j (1 / m) (2 / m) (by positivity) ?_ (by positivity) ?_).mpr hΔ2
    · rw [div_mul_eq_mul_div, div_lt_one hmQ]; linarith
    · rw [div_mul_eq_mul_div, div_lt_one hmQ]; linarith
  -- the point `(p, u)` of `W j × Δ j ♯`
  let y₁ : Fin (n + 1) → P.N := Fin.snoc (Fin.init (h x₀)) u
  have hy₁ : y₁ ∈ secondKind P (W j) (Δ j) := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [y₁, Fin.init_snoc]; exact hj.1
    · simp only [y₁, Fin.snoc_last]; exact hu0
    · simp only [y₁, Fin.snoc_last]; rw [hucode]; exact hΔ1
  have hy₁Y := hprod j hy₁
  have hl : ∀ i, InLattice π m (codeValue (y₁ i)) := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [y₁, Fin.snoc_last]; rw [hucode]
      refine inLattice_qpow_of_dvd P _ ?_
      rw [show (1 / (m : ℚ)) = ((m : ℚ))⁻¹ from one_div _, Rat.inv_natCast_den]
      simp [hmpos.ne']
    · simp only [y₁, Fin.snoc_castSucc]
      obtain ⟨z, hz⟩ := hN₀ j _ hj.1 i
      obtain ⟨c, hc⟩ := hN₀m j
      refine ⟨z * c, ?_⟩
      rw [hc, pow_mul, hz, ← zpow_natCast, ← zpow_mul]
  have hgl := map_lattice P hY g hg ⟨m, hmpos⟩ hy₁Y hl 0
  have hwy : codeValue (g y₁ 0) ^ 2 = qpow π (1 / m) := by
    have h1 := hw (g y₁) (hgX y₁ hy₁Y)
    rw [hhg y₁ hy₁Y, hwprod j y₁ hy₁] at h1
    rw [← h1]; simp only [y₁, Fin.snoc_last]; exact hucode
  obtain ⟨z, hz⟩ := hgl
  have e1 := congrArg ι hz
  have e2 := congrArg ι hwy
  rw [ι_npow, ι_zpow, ← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ] at e1
  rw [ι_npow, hι, ← Nat.cast_smul_eq_nsmul ℚ] at e2
  have e3 : ((2 * z : ℤ) : ℚ) • ι π = (1 : ℚ) • ι π := by
    calc ((2 * z : ℤ) : ℚ) • ι π = (2 : ℚ) • ((z : ℚ) • ι π) := by push_cast; rw [smul_smul]
      _ = (2 : ℚ) • ((m : ℚ) • ι (codeValue (g y₁ 0))) := by rw [← e1]; rfl
      _ = (m : ℚ) • ((2 : ℚ) • ι (codeValue (g y₁ 0))) := smul_comm _ _ _
      _ = (m : ℚ) • ((1 / (m : ℚ)) • ι π) := by rw [← e2]; push_cast; rfl
      _ = (1 : ℚ) • ι π := by rw [smul_smul, mul_one_div_cancel hmQ.ne']
  have e4 := smul_left_injective ℚ he.ne' e3
  have : (2 * z : ℤ) = 1 := by exact_mod_cast e4
  omega

end DiamondIntegral.Section8.Remark87
