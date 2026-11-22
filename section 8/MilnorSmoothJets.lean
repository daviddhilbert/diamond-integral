import «section 8».Lemma86
import «section 8».MilnorSmooth
import «section 8».TruncPairsGen
import «section 8».TruncAmbientGen

/-! (z:coeff:change) for a smooth affine `X`, given étale coordinates at the origin.

Let `X ⊆ 𝔸^N` be cut out near the origin by `F₁, …, F_k ∈ ℂ[y]`, let `f ∈ ℂ[y]` and let
`q = (q₁, …, q_{d+1})` with `q_i(0) = 0`.

**Hypothesis** (`EtaleCoords`, Hensel's lemma; taken as a hypothesis by the author's instruction).
`q` maps the tube `X(𝔪)` onto `𝔪^{d+1}`, and `Φ = (F, q) : 𝔪^N → 𝔪^k × 𝔪^{d+1}` has a `1`-Lipschitz
inverse: `v(y - y') > γ` whenever `v(F(y) - F(y')) > γ` and `v(q(y) - q(y')) > γ`. This holds when
`X = V(F)` is smooth of dimension `d + 1` at `0`, `F` generates its ideal near `0`, `q(0) = 0` and
`q|_X` is étale at `0`, i.e. the Jacobian of `(F, q)` at `0` has rank `N` (multivariable Hensel's
lemma). It implies the chart hypothesis `EtaleChart` of `MilnorSmooth` (`EtaleCoords.chart`).

**Jets.** `IsJetX F f m a`: `a = (a_{i,k})_{i ≤ N, k ≤ m}` with `a_{i,0} = 0`, `F_j(φ_a) ≡ 0` and
`f(φ_a) ≡ s^m mod s^{m+1}`, `φ_a = Σ_k a_{i,k} s^k`: the jets of the manuscript's (f:m:arc) on `X`.
`jetObjectX` is this set with weights `k/m` on `a_{i,k}` (`μ_m` acts by `s ↦ ζ s`). It is the
truncation at level `m` and cutoffs `1` of the concrete set `𝒩 = {y ∈ 𝔪^N | v(F(y)) > 1,
rv(f(y)) = rv(t)}` (`near_coeffSet`).

**Result** (`z_coeff_change_smooth`): `η h_m ∫^◇[𝒳_f] = [𝒳_m] [𝔸]^{-m(d+1)}`. The proof: the first
equality of Lemma 8.6 for objects with form `1` (`zeta_coeff_of_form_one`) gives the normalized class
of the truncation of the trace of the chart fibre `𝒳_f ⊆ 𝔪^{d+1}`; the map `y ↦ q(y)` from `𝒩` to
the chart fibre induces a definable bijection of truncations (`rawClass_eq_of_thickened`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language HahnSeries
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section2 DiamondIntegral.Section3 DiamondIntegral.Section4
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.Hm DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.GammaCells
open DiamondIntegral.Section8.Milnor DiamondIntegral.Section8.RingDefinable DiamondIntegral.Section8.NormalForm
open DiamondIntegral.Section8.Galois SpecialTransformations.Section9

local instance smoothJetStructure : LRV.Structure Carrier := canonicalInterpret
local instance smoothJetModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

variable (P : PuiseuxAmbient) {N d k : ℕ}

local notation "π" => uniformizerValue P

/-! ### The hypothesis -/

/-- **Étale coordinates at the origin (Hensel's lemma).** `q(0) = 0`, `q` maps the tube onto
`𝔪^{d}`, and `(F, q)` has a `1`-Lipschitz inverse on `𝔪^N`. -/
structure EtaleCoords (F : Fin k → MvPolynomial (Fin N) ℂ) (q : Fin d → MvPolynomial (Fin N) ℂ) : Prop where
  zero : ∀ i, MvPolynomial.constantCoeff (q i) = 0
  surj : ∀ x : Fin d → VFType (M := P.N), (∀ i, 1 < Values.vfValueHom (x i)) →
    ∃ y ∈ tube P F, chartMap P q y = x
  lipschitz : ∀ y y' : Fin N → VFType (M := P.N), (∀ l, 1 < Values.vfValueHom (y l)) →
    (∀ l, 1 < Values.vfValueHom (y' l)) → ∀ γ : Values.Gamma (M := P.N),
    (∀ j, γ.val < Values.vfValueHom (MvPolynomial.eval y (fN P (F j)) - MvPolynomial.eval y' (fN P (F j)))) →
    (∀ i, γ.val < Values.vfValueHom (chartMap P q y i - chartMap P q y' i)) →
      ∀ l, γ.val < Values.vfValueHom (y l - y' l)

/-- Étale coordinates give an étale chart. -/
theorem EtaleCoords.chart {F : Fin k → MvPolynomial (Fin N) ℂ} {q : Fin d → MvPolynomial (Fin N) ℂ}
    (h : EtaleCoords P F q) : EtaleChart P F q :=
  ⟨h.zero, h.surj, fun y hy y' hy' γ hq => h.lipschitz y y' hy.1 hy'.1 γ
    (fun j => by rw [hy.2 j, hy'.2 j, sub_self]; exact gamma_lt_value_zero γ) hq⟩

/-- For `X = 𝔸^d` (no equations, `q` the identity), the coordinates are étale: the hypothesis is
satisfiable. -/
theorem etaleCoords_affine :
    EtaleCoords P (fun j : Fin 0 => j.elim0) (fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) ℂ)) := by
  have hmap : ∀ y : Fin d → VFType (M := P.N),
      chartMap P (fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) ℂ)) y = y := by
    intro y
    funext i
    change MvPolynomial.eval y (MvPolynomial.map (ambientComplexFieldHom P.e) (MvPolynomial.X i)) = y i
    rw [MvPolynomial.map_X, MvPolynomial.eval_X]
  refine ⟨fun i => MvPolynomial.constantCoeff_X (R := ℂ) i,
    fun x hx => ⟨x, ⟨hx, fun j => j.elim0⟩, hmap x⟩, ?_⟩
  intro y y' _ _ γ _ h l
  rw [hmap, hmap] at h
  exact h l

/-! ### Concrete points in the ambient -/

/-- Concrete evaluation of a complex polynomial. -/
abbrev cev {n : ℕ} (g : MvPolynomial (Fin n) ℂ) (x : Fin n → Ser) : Ser :=
  MvPolynomial.eval x (MvPolynomial.map puiseuxConstant g)

theorem qpow_one' : qpow π 1 = piV P := by
  have := qpow_intCast (uniformizerValue P) 1
  simpa using this

theorem one_lt_value_eVF_iff (y : Ser) : 1 < Values.vfValueHom (eVF P y) ↔ 0 < ordS y := by
  have h := lt_value_eVF_iff P 0 y
  rw [Hm.qpow_zero' P] at h
  exact h

theorem piV_lt_value_eVF_iff (y : Ser) :
    (piV P).val < Values.vfValueHom (eVF P y) ↔ ((1 : ℚ) : WithTop ℚ) < ordS y := by
  rw [← qpow_one' P]
  exact lt_value_eVF_iff P 1 y

theorem eVF_zero : eVF P 0 = 0 := by rw [eVF_eq, map_zero]

theorem tN_eq_eVF : tN P = eVF P tS := by rw [tS_eq_tSeries, eVF_eq]

theorem one_lt_ordS_of_close {a a' : Ser} (ha : ((1 : ℚ) : WithTop ℚ) < ordS a)
    (h : ((1 : ℚ) : WithTop ℚ) < ordS (a - a')) : ((1 : ℚ) : WithTop ℚ) < ordS a' := by
  have he : a' = a + -(a - a') := by ring
  rw [he]
  refine lt_of_lt_of_le (lt_min ha ?_) (ordS_add _ _)
  rwa [ordS_neg]

theorem one_lt_ordS_sub {a a' : Ser} (ha : ((1 : ℚ) : WithTop ℚ) < ordS a)
    (ha' : ((1 : ℚ) : WithTop ℚ) < ordS a') : ((1 : ℚ) : WithTop ℚ) < ordS (a - a') :=
  lt_of_lt_of_le (lt_min ha ha') (ordS_sub _ _)

/-- Polynomials with complex coefficients preserve `m`-rationality. -/
theorem rational_cev (m : ℕ+) {n : ℕ} (g : MvPolynomial (Fin n) ℂ) {x : Fin n → Ser}
    (hx : ∀ l, IsRational m (x l)) : IsRational m (cev g x) := by
  rw [← fixed_iff_rational]
  set σ := puiseuxRootSystemAction (k := ℂ) (levelRoots m)
  have hC : (σ : Ser →+* Ser).comp puiseuxConstant = puiseuxConstant :=
    RingHom.ext fun c => σ.commutes ⟨puiseuxConstant c, const_mem_base c⟩
  have hx' : (σ : Ser →+* Ser) ∘ x = x := funext fun l => by
    show σ (x l) = x l
    exact (fixed_iff_rational m (x l)).mpr (hx l)
  unfold cev
  rw [MvPolynomial.eval_map]
  have h := MvPolynomial.eval₂_comp_left (σ : Ser →+* Ser) puiseuxConstant x g
  rw [hC, hx'] at h
  show (σ : Ser →+* Ser) _ = _
  exact h

include P in
theorem integral_cev {n : ℕ} (g : MvPolynomial (Fin n) ℂ) (hg : MvPolynomial.constantCoeff g = 0)
    {x : Fin n → Ser} (hx : ∀ l, 0 < ordS (x l)) : 0 < ordS (cev g x) := by
  rw [← one_lt_value_eVF_iff P, ← eval_eVF]
  exact poly_maximal P g hg (fun l => (one_lt_value_eVF_iff P (x l)).mpr (hx l))

/-! ### Polynomial `rv` conditions over `ℂ((t))` -/

/-- A polynomial over `ℂ((t^{1/∞}))` in the field sort of the concrete model. -/
def gS {n : ℕ} (g : MvPolynomial (Fin n) Ser) : MvPolynomial (Fin n) (VFType (M := Carrier)) :=
  MvPolynomial.map taggedFieldEquiv.symm.toRingHom g

/-- `{z | rv(g(z)) = rv(t)}`. -/
def rvTSet {n : ℕ} (g : MvPolynomial (Fin n) Ser) : Set (Fin (n + 0) → Carrier) :=
  {z | iRv (SpecialTransformations.Section5.mvPolynomialCode (gS g) (codesOf z)) = iRv (vfOf tS).val}

theorem rvTSet_definable {n : ℕ} (g : MvPolynomial (Fin n) Ser)
    (hg : ∀ c, g.coeff c ∈ puiseuxBaseSubfield ℂ) : {c | baseCarrier c}.Definable LRV (rvTSet g) := by
  have ht : (vfOf tS).val ∈ {c : Carrier | baseCarrier c} :=
    base_mem_of tS puiseuxBaseUniformizer.property
  have hcoeff : ∀ c, ((gS g).coeff c).val ∈ {c : Carrier | baseCarrier c} := by
    intro c
    rw [gS, MvPolynomial.coeff_map]
    exact base_mem_of _ (hg c)
  have hp := SpecialTransformations.Section5.mvPolynomialCode_definable (m := 0)
    (S := {c : Carrier | baseCarrier c}) (gS g) hcoeff
  change @Set.DefinableFun Carrier LRV (CanonicalStructure.normalize (M := Carrier)) (Fin n ⊕ Fin 0)
    {c : Carrier | baseCarrier c} (SpecialTransformations.Section5.mvPolynomialCode (m := 0) (gS g)) at hp
  rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical] at hp
  have hcodes : {c : Carrier | baseCarrier c}.DefinableMap LRV (codesOf (d := n)) := by
    intro a
    cases a with
    | inl i => exact Set.DefinableFun.proj LRV
    | inr i => exact i.elim0
  have hF : {c : Carrier | baseCarrier c}.DefinableFun LRV
      (fun z : Fin (n + 0) → Carrier => iRv (SpecialTransformations.Section5.mvPolynomialCode (gS g) (codesOf z))) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := Carrier) (L := LRV) Fn.rvMap)).comp
      (show {c : Carrier | baseCarrier c}.DefinableMap LRV
          (fun z : Fin (n + 0) → Carrier => ![SpecialTransformations.Section5.mvPolynomialCode (gS g) (codesOf z)]) from by
        intro a
        fin_cases a
        exact hp.comp hcodes)
  have hG : {c : Carrier | baseCarrier c}.DefinableFun LRV (fun _ : Fin (n + 0) → Carrier => iRv (vfOf tS).val) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := Carrier) (L := LRV) Fn.rvMap)).comp
      (show {c : Carrier | baseCarrier c}.DefinableMap LRV (fun _ : Fin (n + 0) → Carrier => ![(vfOf tS).val]) from by
        intro a
        fin_cases a
        exact LRV.definableFun_const _ ht)
  exact hF.ofPred_eq hG

theorem mem_rvTSet {n : ℕ} (g : MvPolynomial (Fin n) Ser) (z : Fin (n + 0) → Carrier) (x : Fin n → Ser)
    (hz : ∀ i, z i = Sum.inl (x i)) :
    z ∈ rvTSet g ↔ rvOfField (MvPolynomial.eval x g) = rvOfField tS := by
  change iRv _ = iRv _ ↔ _
  have hcode := SpecialTransformations.Section5.mvPolynomialCode_eq (gS g) (codesOf z)
    (fun i => vfOf (x i)) (fun i => by rw [codesOf, Sum.elim_inl, hz i]; rfl)
  rw [hcode, iRv_val, iRv_val, RingEquiv.apply_symm_apply]
  have he : taggedFieldEquiv (MvPolynomial.eval (fun i => vfOf (x i)) (gS g)) = MvPolynomial.eval x g := by
    rw [gS, MvPolynomial.eval_map]
    have h := MvPolynomial.eval₂_comp_left taggedFieldEquiv.toRingHom taggedFieldEquiv.symm.toRingHom
      (fun i => vfOf (x i)) g
    have hc : taggedFieldEquiv.toRingHom.comp taggedFieldEquiv.symm.toRingHom = RingHom.id Ser :=
      RingHom.ext fun c => taggedFieldEquiv.apply_symm_apply _
    have hx : (taggedFieldEquiv.toRingHom ∘ fun i => vfOf (x i)) = x := by
      funext i
      exact taggedFieldEquiv.apply_symm_apply _
    rw [hc, hx] at h
    exact h
  rw [he]
  constructor
  · intro h; exact Sum.inr_injective h
  · intro h; rw [h]

/-- `rv(t + w) = rv(t)` iff `v(w) > 1`. -/
theorem rv_add_tS_iff (w : Ser) : rvOfField (tS + w) = rvOfField tS ↔ ((1 : ℚ) : WithTop ℚ) < ordS w := by
  have htord : (tS : HahnSeries ℚ ℂ).order = 1 := by
    rw [puiseuxRoot_coe, order_single one_ne_zero]; norm_num
  have htlead : (tS : HahnSeries ℚ ℂ).leadingCoeff = 1 := by
    rw [leadingCoeff_eq, htord, puiseuxRoot_coe]; simp
  constructor
  · intro h
    have hne := ne_zero_of_rvOfField_eq tS_ne_zero h
    have hne' : ((tS + w : Ser) : HahnSeries ℚ ℂ) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    obtain ⟨hord, hlead⟩ := (rvOfField_eq_iff hne tS_ne_zero).mp h
    rw [htord] at hord
    rw [htlead, leadingCoeff_eq, hord] at hlead
    rw [lt_ordS_iff]
    intro γ hγ
    have hd : cf w γ = cf (tS + w) γ - cf tS γ := by
      change (w : HahnSeries ℚ ℂ).coeff γ = ((tS : HahnSeries ℚ ℂ) + (w : HahnSeries ℚ ℂ)).coeff γ -
        (tS : HahnSeries ℚ ℂ).coeff γ
      rw [HahnSeries.coeff_add]; ring
    rw [hd]
    rcases lt_or_eq_of_le hγ with hlt | rfl
    · have h1 : cf (tS + w) γ = 0 := by
        apply coeff_eq_zero_of_lt_order
        rw [hord]; exact hlt
      have h2 : cf tS γ = 0 := by
        apply coeff_eq_zero_of_lt_order
        rw [htord]; exact hlt
      rw [h1, h2, sub_zero]
    · have h2 : cf tS 1 = 1 := by
        change (tS : HahnSeries ℚ ℂ).coeff 1 = 1
        rw [← htord, ← leadingCoeff_eq, htlead]
      change ((tS + w : Ser) : HahnSeries ℚ ℂ).coeff 1 - cf tS 1 = 0
      rw [hlead, h2, sub_self]
  · intro h
    apply rvOfField_eq_of_close tS_ne_zero
    rw [add_sub_cancel_left, ordS_tS]
    exact h

/-! ### The set `𝒩 = {y ∈ 𝔪^N | v(F(y)) > 1, rv(f(y)) = rv(t)}` and the jets of `X` -/

variable (F : Fin k → MvPolynomial (Fin N) ℂ) (f : MvPolynomial (Fin N) ℂ)

/-- `t + g` over `ℂ((t))`. -/
def tPlus (g : MvPolynomial (Fin N) ℂ) : MvPolynomial (Fin N) Ser :=
  MvPolynomial.C tS + MvPolynomial.map puiseuxConstant g

theorem tPlus_coeff_mem (g : MvPolynomial (Fin N) ℂ) (c : Fin N →₀ ℕ) :
    (tPlus g).coeff c ∈ puiseuxBaseSubfield ℂ := by
  have h : (tPlus g).coeff c = (MvPolynomial.C tS : MvPolynomial (Fin N) Ser).coeff c +
      (MvPolynomial.map puiseuxConstant g).coeff c := by
    unfold tPlus
    simp
  rw [h, MvPolynomial.coeff_C, MvPolynomial.coeff_map]
  refine add_mem ?_ (const_mem_base _)
  split_ifs
  · exact puiseuxBaseUniformizer.property
  · exact zero_mem _

/-- `𝒩` as a set of raw tuples of the concrete model. -/
def rawNear : Set (Fin (N + 0) → Carrier) :=
  rawMilnor f ∩ ⋂ j, rvTSet (tPlus (F j))

theorem rawNear_definable : {c | baseCarrier c}.Definable LRV (rawNear F f) :=
  (rawMilnor_definable f).inter
    (Set.definable_iInter_of_finite fun j => rvTSet_definable (tPlus (F j)) (tPlus_coeff_mem (F j)))

theorem rawNear_definableOver : DefinableOver {c | baseCarrier c} (mixedSorts N 0) (rawNear F f) := by
  refine (definableOver_iff_normalized_raw _ _ _).mpr ⟨?_, ?_⟩
  · rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical]
    exact rawNear_definable F f
  · intro z hz i
    rw [mixedSorts_zero]
    exact (hz.1.1 i).2.1

/-- The points of `𝒩`. -/
theorem mem_mixedSet_near (p : (Fin N → Ser) × (Fin 0 → RV)) :
    p ∈ mixedSet (rawNear F f) ↔ (∀ i, 0 < ordS (p.1 i)) ∧
      rvOfField (cev f p.1) = rvOfField tS ∧ ∀ j, ((1 : ℚ) : WithTop ℚ) < ordS (cev (F j) p.1) := by
  have h1 : p ∈ mixedSet (rawMilnor f) ↔ _ := mem_mixedSet_milnor f p
  change mixedRaw p ∈ rawMilnor f ∩ ⋂ j, rvTSet (tPlus (F j)) ↔ _
  rw [Set.mem_inter_iff, Set.mem_iInter]
  change p ∈ mixedSet (rawMilnor f) ∧ _ ↔ _
  rw [h1, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun j => ?_
  rw [mem_rvTSet (tPlus (F j)) (mixedRaw p) p.1 (mixedRaw_zero p), ← rv_add_tS_iff]
  rw [tPlus, MvPolynomial.eval_add, MvPolynomial.eval_C]

/-- `𝒩` is invariant for the cutoffs `(1, …, 1)`. -/
theorem near_invariant (m : ℕ+) : Invariant m (bOne m) (mixedSet (rawNear F f)) := by
  intro x x' u hx hcongr
  have hx1 := (mem_mixedSet_near F f (x, u)).mp hx
  have hm : (x, u) ∈ mixedSet (rawMilnor f) := (mem_mixedSet_milnor f (x, u)).mpr ⟨hx1.1, hx1.2.1⟩
  have hm' := milnor_invariant_conc f m x x' u hm hcongr
  obtain ⟨hx'M, hx'f⟩ := (mem_mixedSet_milnor f (x', u)).mp hm'
  have hdiff : ∀ i, ((1 : ℚ) : WithTop ℚ) < ordS (x i - x' i) := by
    intro i
    rw [lt_ordS_iff]
    intro γ hγ
    have : cf (x i - x' i) γ = cf (x i) γ - cf (x' i) γ := by
      change (x i : HahnSeries ℚ ℂ).coeff γ - (x' i : HahnSeries ℚ ℂ).coeff γ = _
      rfl
    rw [this, hcongr i γ (by rw [lev_self]; exact hγ), sub_self]
  refine (mem_mixedSet_near F f (x', u)).mpr ⟨hx'M, hx'f, fun j => ?_⟩
  exact one_lt_ordS_of_close (hx1.2.2 j)
    (poly_lipschitz_conc (F j) (fun i => (hx1.1 i).le) (fun i => (hx'M i).le) hdiff)

/-- **The jets of `X`**: `a_{i,0} = 0`, `F_j(φ_a) ≡ 0` and `f(φ_a) ≡ s^m mod s^{m+1}`. -/
def IsJetX (m : ℕ+) (a : Fin N → Fin ((m : ℕ) + 1) → ℂ) : Prop :=
  IsJet f m a ∧ ∀ j, ∀ l ≤ (m : ℕ), (jetPoly (F j) m a).coeff l = 0

theorem one_lt_ordS_sub_iff (m : ℕ+) (g : Polynomial ℂ) :
    ((1 : ℚ) : WithTop ℚ) < ordS (sub m g) ↔ ∀ l ≤ (m : ℕ), g.coeff l = 0 := by
  have hm : (0 : ℚ) < ((m : ℕ) : ℚ) := by exact_mod_cast m.pos
  have hle : ∀ l : ℕ, lev m l ≤ 1 ↔ l ≤ (m : ℕ) := by
    intro l
    rw [lev, div_le_one hm]
    exact_mod_cast Iff.rfl
  rw [lt_ordS_iff]
  constructor
  · intro h l hl
    rw [← cf_sub_lev m g l]
    exact h _ ((hle l).mpr hl)
  · intro h γ hγ
    by_cases hl : ∃ l : ℕ, γ = lev m l
    · obtain ⟨l, rfl⟩ := hl
      rw [cf_sub_lev]
      exact h l ((hle l).mp hγ)
    · push Not at hl
      exact cf_sub_of_not_lev m g γ hl

/-- **The coefficient set of the truncation of `𝒩` is the set of jets of `X`.** -/
theorem near_coeffSet (m : ℕ+) (c : Idx (bOne (d := N) m) ⊕ Fin 0 → ℂ) :
    c ∈ coeffSet m (bOne m) Fin.elim0 (mixedSet (rawNear F f)) ↔
      IsJetX F f m (fun i k => c (.inl ⟨i, k⟩)) := by
  change (polyRep m (bOne m) (fun k => c (.inl k)), labelRep m Fin.elim0 (fun j => c (.inr j))) ∈
    mixedSet (rawNear F f) ↔ _
  rw [mem_mixedSet_near]
  simp only [cev]
  rw [eval_polyRep, rv_sub_eq_tS_iff]
  unfold IsJetX IsJet
  simp only [and_assoc]
  refine and_congr (forall_congr' fun i => pos_ordS_polyRep m _ i)
    (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  refine forall_congr' fun j => ?_
  rw [eval_polyRep, one_lt_ordS_sub_iff]

/-- **The jet variety `𝒳_m` of `X`** with its `μ_m`-action, as a diagonal constructible object: the
truncation of `𝒩` at level `m` and cutoffs `1`. -/
def jetObjectX (m : ℕ+) : DiagonalConstructible.Object :=
  truncObject m (bOne m) Fin.elim0 (rawNear_definableOver F f) (jetEnum (d := N) m)

theorem jetObjectX_domain (m : ℕ+) :
    (jetObjectX F f m).domain = {x | IsJetX F f m (fun i k => x (jetEnum m (.inl ⟨i, k⟩)))} := by
  change (truncObject m (bOne m) Fin.elim0 (rawNear_definableOver F f) (jetEnum m)).domain = _
  rw [truncObject_domain]
  ext x
  exact near_coeffSet F f m (x ∘ jetEnum m)

/-- The coordinate `a_{i,k}` has weight `k/m`: `μ_m` acts by `s ↦ ζ s`. -/
theorem jetObjectX_weights (m : ℕ+) (i : Fin N) (k : Fin ((m : ℕ) + 1)) :
    (jetObjectX F f m).weights (jetEnum m (.inl ⟨i, k⟩)) = lev m k := by
  change (truncObject m (bOne m) Fin.elim0 (rawNear_definableOver F f) (jetEnum m)).weights _ = _
  rw [truncObject_weights]
  simp [stdWt]

/-- `[𝒳_m]` for `X`. -/
def jetClassX (m : ℕ+) : EquivariantVariety.ModifiedRing := dcClass (jetObjectX F f m)

/-! ### The chart fibre -/

variable (q : Fin (d + 1) → MvPolynomial (Fin N) ℂ)

/-- The trace of the chart fibre `𝒳_f ⊆ 𝔪^{d+1}` on the concrete model. -/
abbrev chartTrace : Set (Fin ((d + 1) + 0) → Carrier) := strace P 0 (milnorDefSetX P F f q)

theorem mem_chartTrace (p : (Fin (d + 1) → Ser) × (Fin 0 → RV)) :
    p ∈ mixedSet (chartTrace P F f q) ↔ ePoint P p ∈ milnorSetX P F f q := by
  rw [mem_strace, unscaleP_zero]
  exact Iff.rfl

theorem rad_bOne (m : ℕ+) (i : Fin (d + 1)) : rad P m (bOne m) 0 i = piV P := by
  simp only [rad, bOne, lev_self, Nat.cast_zero, sub_zero]
  exact qpow_one' P

variable {P F f q}

/-- The chart fibre is invariant for the cutoffs `(1, …, 1)`. -/
theorem chart_invariant (hq : EtaleChart P F q) (m : ℕ+) :
    Invariant m (bOne m) (mixedSet (chartTrace P F f q)) :=
  invariant_strace P m (bOne m) 0 (milnorDefSetX P F f q) (fun a ha x hx =>
    milnorX_invariant P f hq (x := a.1) (t := a.2) ha (fun i => by
      have h := hx i
      rwa [rad_bOne] at h))

theorem chart_pos (hq : EtaleChart P F q) {p : (Fin (d + 1) → Ser) × (Fin 0 → RV)}
    (hp : p ∈ mixedSet (chartTrace P F f q)) (i : Fin (d + 1)) : 0 < ordS (p.1 i) := by
  rw [mem_chartTrace] at hp
  exact (one_lt_value_eVF_iff P _).mp
    (milnorX_maximal P f hq (x := (ePoint P p).1) (t := (ePoint P p).2) hp i)

theorem chart_rationalIntegral (hq : EtaleChart P F q) (m : ℕ+) :
    RationalIntegral m (mixedSet (chartTrace P F f q)) := fun _ hp _ i =>
  isIntegral_of_ordS (le_of_lt (chart_pos hq hp i))

variable (P F f q)

/-- The chart onto the fibre. -/
def chartCo : Map (sourceDefSet P F f) (milnorDefSetX P F f q) :=
  ⟨fun a => ⟨(chartDefMap P F f q a).val, ⟨a, rfl⟩⟩, (chartDefMap P F f q).graph_definable⟩

variable {P F f q}

theorem chartCo_bijective (hq : EtaleChart P F q) : Function.Bijective (chartCo P F f q) := by
  constructor
  · intro a a' h
    have h2 : (chartCo P F f q a).val = (chartCo P F f q a').val := congrArg Subtype.val h
    change (chartDefMap P F f q a).val = (chartDefMap P F f q a').val at h2
    rw [chartDefMap_val, chartDefMap_val] at h2
    have h1 : chartMap P q a.val.1 = chartMap P q a'.val.1 := congrArg Prod.fst h2
    apply Subtype.ext
    refine Prod.ext (funext fun l => ?_) (funext fun j => j.elim0)
    by_contra hne
    have hne' : a.val.1 l - a'.val.1 l ≠ 0 := sub_ne_zero.mpr hne
    let γ : Values.Gamma (M := P.N) := ⟨Values.vfValueHom (a.val.1 l - a'.val.1 l), by
      rw [Values.infinity_eq_zero]; exact (map_ne_zero _).mpr hne'⟩
    have := hq.lipschitz a.val.1 a.property.1 a'.val.1 a'.property.1 γ
      (fun i => by rw [h1, sub_self]; exact gamma_lt_value_zero γ) l
    exact lt_irrefl _ this
  · intro c
    obtain ⟨a, ha⟩ := c.property
    exact ⟨a, Subtype.ext ha⟩

/-- **Rational points of the chart fibre lift to rational points of the tube.** -/
theorem chart_lift (hq : EtaleChart P F q) (m : ℕ+) (p : (Fin (d + 1) → Ser) × (Fin 0 → RV))
    (hp : p ∈ mixedSet (chartTrace P F f q)) (hr : RationalPoint m p) :
    ∃ y : Fin N → Ser, (∀ l, IsRational m (y l)) ∧ (∀ l, 0 < ordS (y l)) ∧ (∀ j, cev (F j) y = 0) ∧
      rvOfField (cev f y) = rvOfField tS ∧ ∀ i, cev (q i) y = p.1 i := by
  rw [mem_chartTrace] at hp
  let H := invMapG P (chartCo P F f q) (chartCo_bijective (f := f) hq)
  obtain ⟨p0, hp0⟩ := exists_concrete_imageG P H p hp
  have hr0 := concrete_image_rationalG P H m p hp p0 hp0 hr
  have hmem := (H ⟨ePoint P p, hp⟩).property
  rw [hp0] at hmem
  have happ := apply_invMapG P (chartCo P F f q) (chartCo_bijective (f := f) hq) ⟨ePoint P p, hp⟩
  have hval : (chartDefMap P F f q (H ⟨ePoint P p, hp⟩)).val = ePoint P p := congrArg Subtype.val happ
  rw [chartDefMap_val] at hval
  have hch : chartMap P q (H ⟨ePoint P p, hp⟩).val.1 = (ePoint P p).1 := congrArg Prod.fst hval
  rw [hp0] at hch
  refine ⟨p0.1, hr0.1, fun l => (one_lt_value_eVF_iff P _).mp (hmem.1.1 l), fun j => ?_, ?_, fun i => ?_⟩
  · have h := hmem.1.2 j
    change MvPolynomial.eval (fun l => eVF P (p0.1 l)) (fN P (F j)) = 0 at h
    rw [eval_eVF, ← eVF_zero P] at h
    exact eVF_injective P h
  · have h := hmem.2
    change rv P.N (MvPolynomial.eval (fun l => eVF P (p0.1 l)) (fN P f)) = rv P.N (tN P) at h
    rwa [eval_eVF, tN_eq_eVF, rv_eVF_iff] at h
  · have h := congrFun hch i
    change MvPolynomial.eval (fun l => eVF P (p0.1 l)) (fN P (q i)) = eVF P (p.1 i) at h
    rw [eval_eVF] at h
    exact eVF_injective P h

/-- **`q` maps `𝒩` into the chart fibre.** -/
theorem chart_maps (hc : EtaleCoords P F q) {p : (Fin N → Ser) × (Fin 0 → RV)}
    (hp : p ∈ mixedSet (rawNear F f)) :
    ((fun i => cev (q i) p.1), p.2) ∈ mixedSet (chartTrace P F f q) := by
  rw [mem_chartTrace]
  obtain ⟨hpos, hrv, hF⟩ := (mem_mixedSet_near F f p).mp hp
  have hye : ∀ l, 1 < Values.vfValueHom (eVF P (p.1 l)) := fun l => (one_lt_value_eVF_iff P _).mpr (hpos l)
  have hx : ∀ i, 1 < Values.vfValueHom (eVF P (cev (q i) p.1)) := fun i =>
    (one_lt_value_eVF_iff P _).mpr (integral_cev P (q i) (hc.zero i) hpos)
  obtain ⟨y, hy, hyq⟩ := hc.surj (fun i => eVF P (cev (q i) p.1)) hx
  have hlip := hc.lipschitz y (fun l => eVF P (p.1 l)) hy.1 hye (piV P) (fun j => by
      rw [hy.2 j, zero_sub, vfValue_neg, eval_eVF]
      exact (piV_lt_value_eVF_iff P _).mpr (hF j))
    (fun i => by
      rw [hyq]
      show (piV P).val < Values.vfValueHom (eVF P (cev (q i) p.1) -
        MvPolynomial.eval (fun l => eVF P (p.1 l)) (fN P (q i)))
      rw [eval_eVF, sub_self]
      exact gamma_lt_value_zero _)
  have hfl := poly_lipschitz P f (fun l => (hy.1 l).le) (fun l => (hye l).le) hlip
  have hfe : rv P.N (MvPolynomial.eval (fun l => eVF P (p.1 l)) (fN P f)) = rv P.N (tN P) := by
    rw [eval_eVF, tN_eq_eVF, rv_eVF_iff]
    exact hrv
  have hfy : Values.vfValueHom (MvPolynomial.eval (fun l => eVF P (p.1 l)) (fN P f)) = (piV P).val := by
    rw [← value_tN]
    exact congrArg Values.vrv hfe
  have hne : MvPolynomial.eval (fun l => eVF P (p.1 l)) (fN P f) ≠ 0 := by
    intro h0
    rw [h0, map_zero, ← Values.infinity_eq_zero] at hfy
    exact (piV P).property hfy.symm
  have hrvy : rv P.N (MvPolynomial.eval y (fN P f)) = rv P.N (tN P) := by
    rw [← hfe]
    apply DiamondIntegral.Section6.rv_eq_of_value_close hne
    change Values.vfValueHom _ < Values.vfValueHom _
    rw [hfy]
    exact hfl
  exact (mem_milnorSetX_iff P F f q (fun i => eVF P (cev (q i) p.1)) (fun j => eRV P (p.2 j))).mpr
    ⟨y, hy, hrvy, hyq⟩

/-- **`q` respects truncations on `𝒩`**, by the Lipschitz property of `(F, q)⁻¹`. -/
theorem chart_resp (hc : EtaleCoords P F q) {p p' : (Fin N → Ser) × (Fin 0 → RV)}
    (hp : p ∈ mixedSet (rawNear F f)) (hp' : p' ∈ mixedSet (rawNear F f)) :
    (∀ l, ((1 : ℚ) : WithTop ℚ) < ordS (p.1 l - p'.1 l)) ↔
      ∀ i, ((1 : ℚ) : WithTop ℚ) < ordS (cev (q i) p.1 - cev (q i) p'.1) := by
  obtain ⟨hpos, -, hF⟩ := (mem_mixedSet_near F f p).mp hp
  obtain ⟨hpos', -, hF'⟩ := (mem_mixedSet_near F f p').mp hp'
  constructor
  · intro h i
    exact poly_lipschitz_conc (q i) (fun l => (hpos l).le) (fun l => (hpos' l).le) h
  · intro h l
    have := hc.lipschitz (fun l => eVF P (p.1 l)) (fun l => eVF P (p'.1 l))
      (fun l => (one_lt_value_eVF_iff P _).mpr (hpos l)) (fun l => (one_lt_value_eVF_iff P _).mpr (hpos' l))
      (piV P) (fun j => by
        rw [eval_eVF, eval_eVF, ← eVF_sub, piV_lt_value_eVF_iff]
        exact one_lt_ordS_sub (hF j) (hF' j))
      (fun i => by
        show (piV P).val < Values.vfValueHom (MvPolynomial.eval (fun l => eVF P (p.1 l)) (fN P (q i)) -
          MvPolynomial.eval (fun l => eVF P (p'.1 l)) (fN P (q i)))
        rw [eval_eVF, eval_eVF, ← eVF_sub, piV_lt_value_eVF_iff]
        exact h i) l
    rwa [← eVF_sub, piV_lt_value_eVF_iff] at this

/-! ### The correspondence `𝒩 → 𝒳_f`, `y ↦ q(y)` -/

variable (q)

/-- `y ↦ q(y)` on concrete points. -/
def phiQ (p : (Fin N → Ser) × (Fin 0 → RV)) : (Fin (d + 1) → Ser) × (Fin 0 → RV) :=
  (fun i => cev (q i) p.1, p.2)

variable {q}

include P in
theorem RI_phiQ (hz : ∀ i, MvPolynomial.constantCoeff (q i) = 0) (m : ℕ+)
    {p : (Fin N → Ser) × (Fin 0 → RV)} (hp : ∀ l, 0 < ordS (p.1 l)) (hr : RI m p) :
    RI m (phiQ q p) :=
  ⟨fun i => ⟨rational_cev m (q i) (fun l => (hr.1 l).1),
    isIntegral_of_ordS (le_of_lt (integral_cev P (q i) (hz i) hp))⟩, fun j => j.elim0⟩

theorem one_lt_ordS_of_cf {a b : Ser} (h : ∀ γ ≤ (1 : ℚ), cf a γ = cf b γ) :
    ((1 : ℚ) : WithTop ℚ) < ordS (a - b) := by
  rw [lt_ordS_iff]
  intro γ hγ
  have : cf (a - b) γ = cf a γ - cf b γ := by
    change (a : HahnSeries ℚ ℂ).coeff γ - (b : HahnSeries ℚ ℂ).coeff γ = _
    rfl
  rw [this, h γ hγ, sub_self]

/-- The complex polynomial `q_i(y) - x_i` in the variables `(y, x)`. -/
def gq (q : Fin (d + 1) → MvPolynomial (Fin N) ℂ) (i : Fin (d + 1)) : MvPolynomial (Fin (N + (d + 1))) ℂ :=
  MvPolynomial.rename (Fin.castAdd (d + 1)) (q i) - MvPolynomial.X (Fin.natAdd N i)

theorem cev_gq (i : Fin (d + 1)) (y : Fin N → Ser) (x : Fin (d + 1) → Ser) :
    cev (gq q i) (Fin.append y x) = cev (q i) y - x i := by
  unfold cev gq
  rw [(MvPolynomial.map puiseuxConstant).map_sub, MvPolynomial.map_X, (MvPolynomial.eval (Fin.append y x)).map_sub,
    MvPolynomial.eval_X, Fin.append_right, MvPolynomial.map_rename, MvPolynomial.eval_rename]
  have hy : Fin.append y x ∘ Fin.castAdd (d + 1) = y := funext fun l => Fin.append_left y x l
  rw [hy]

theorem rv_tPlus_iff {n : ℕ} (g : MvPolynomial (Fin n) ℂ) (x : Fin n → Ser) :
    rvOfField (MvPolynomial.eval x (tPlus g)) = rvOfField tS ↔ ((1 : ℚ) : WithTop ℚ) < ordS (cev g x) := by
  rw [tPlus, MvPolynomial.eval_add, MvPolynomial.eval_C, rv_add_tS_iff]

variable (P F f q)

/-- The index maps of the two points of a pair. -/
abbrev ιL (i : Fin N) : Fin ((N + (d + 1)) + (0 + 0)) := Fin.castAdd (0 + 0) (Fin.castAdd (d + 1) i)
abbrev ιR (i : Fin (d + 1)) : Fin ((N + (d + 1)) + (0 + 0)) := Fin.castAdd (0 + 0) (Fin.natAdd N i)
abbrev ιV (v : Fin (N + (d + 1))) : Fin ((N + (d + 1)) + (0 + 0)) := Fin.castAdd (0 + 0) v

/-- **The thickened graph** `{(y, x) | y ∈ 𝒩, x ∈ 𝒳_f, v(q(y) - x) > 1}`. -/
def rawW : Set (Fin ((N + (d + 1)) + (0 + 0)) → Carrier) :=
  (fun g => g ∘ ιL (d := d)) ⁻¹' rawNear F f ∩
    ((fun g => g ∘ ιR (N := N)) ⁻¹' chartTrace P F f q ∩
      ⋂ i, (fun g => g ∘ ιV) ⁻¹' rvTSet (tPlus (gq q i)))

variable {P F f q}

theorem chartTrace_definable :
    {c | baseCarrier c}.Definable LRV (chartTrace P F f q) := by
  have h := ((definableOver_iff_normalized_raw _ _ _).mp (strace_definableOver P 0 (milnorDefSetX P F f q))).1
  rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical] at h
  exact h

theorem rawW_definableOver :
    DefinableOver {c | baseCarrier c} (mixedSorts (N + (d + 1)) (0 + 0)) (rawW P F f q) := by
  refine (definableOver_iff_normalized_raw _ _ _).mpr ⟨?_, ?_⟩
  · rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical]
    exact ((rawNear_definable F f).preimage_comp _).inter ((chartTrace_definable.preimage_comp _).inter
      (Set.definable_iInter_of_finite fun i =>
        (rvTSet_definable (tPlus (gq q i)) (tPlus_coeff_mem (gq q i))).preimage_comp _))
  · intro z hz i
    have hsR := ((definableOver_iff_normalized_raw _ _ _).mp
      (strace_definableOver P 0 (milnorDefSetX P F f q))).2 _ hz.2.1
    refine Fin.addCases (fun v => ?_) (fun j => absurd j.isLt (by simp)) i
    have hs : mixedSorts (N + (d + 1)) (0 + 0) (Fin.castAdd (0 + 0) v) = .vf := by
      show Fin.addCases (motive := fun _ => SortTag) (fun _ => SortTag.vf) (fun _ => SortTag.rv)
        (Fin.castAdd (0 + 0) v) = SortTag.vf
      exact Fin.addCases_left v
    rw [hs]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) v
    · exact (hz.1.1.1 a).2.1
    · have h := hsR b
      rw [mixedSorts_zero] at h
      exact h

theorem mixedRaw_joinG_L (p : (Fin N → Ser) × (Fin 0 → RV)) (p' : (Fin (d + 1) → Ser) × (Fin 0 → RV)) :
    mixedRaw (joinG p p') ∘ ιL (d := d) = mixedRaw p := by
  funext i
  simp only [Function.comp_apply, mixedRaw, joinG, Fin.append_left]
  exact (mixedRaw_zero p i).symm

theorem mixedRaw_joinG_R (p : (Fin N → Ser) × (Fin 0 → RV)) (p' : (Fin (d + 1) → Ser) × (Fin 0 → RV)) :
    mixedRaw (joinG p p') ∘ ιR (N := N) = mixedRaw p' := by
  funext i
  simp only [Function.comp_apply, mixedRaw, joinG, Fin.append_left, Fin.append_right]
  exact (mixedRaw_zero p' i).symm

/-- The points of the thickened graph. -/
theorem mem_rawW (p : (Fin N → Ser) × (Fin 0 → RV)) (p' : (Fin (d + 1) → Ser) × (Fin 0 → RV)) :
    joinG p p' ∈ mixedSet (rawW P F f q) ↔ p ∈ mixedSet (rawNear F f) ∧
      p' ∈ mixedSet (chartTrace P F f q) ∧ ∀ i, ((1 : ℚ) : WithTop ℚ) < ordS (cev (q i) p.1 - p'.1 i) := by
  change mixedRaw (joinG p p') ∈ rawW P F f q ↔ _
  simp only [rawW, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter]
  rw [mixedRaw_joinG_L, mixedRaw_joinG_R]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun i => ?_))
  rw [mem_rvTSet (tPlus (gq q i)) _ (Fin.append p.1 p'.1) (fun v => by
    simp only [Function.comp_apply, mixedRaw, joinG, Fin.append_left]), rv_tPlus_iff, cev_gq]

theorem rawW_invariant (hq : EtaleChart P F q) (m : ℕ+) :
    Invariant m (Fin.append (bOne (d := N) m) (bOne (d := d + 1) m)) (mixedSet (rawW P F f q)) := by
  intro x x' u hx hc
  have e : (x, u) = joinG (leftG (x, u)) (rightG (x, u)) := (joinG_left_right _).symm
  have e' : (x', u) = joinG (leftG (x', u)) (rightG (x', u)) := (joinG_left_right _).symm
  rw [e, mem_rawW] at hx
  rw [e', mem_rawW]
  obtain ⟨hL, hR, hcl⟩ := hx
  have hcL : ∀ (i : Fin N) (γ : ℚ), γ ≤ lev m (bOne m i) →
      cf ((leftG (x, u)).1 i) γ = cf ((leftG (x', u)).1 i) γ := fun i γ hγ =>
    hc (Fin.castAdd (d + 1) i) γ (by rw [Fin.append_left]; exact hγ)
  have hcR : ∀ (i : Fin (d + 1)) (γ : ℚ), γ ≤ lev m (bOne m i) →
      cf ((rightG (x, u)).1 i) γ = cf ((rightG (x', u)).1 i) γ := fun i γ hγ =>
    hc (Fin.natAdd N i) γ (by rw [Fin.append_right]; exact hγ)
  have hL' : leftG (x', u) ∈ mixedSet (rawNear F f) :=
    near_invariant F f m (leftG (x, u)).1 (leftG (x', u)).1 (leftG (x, u)).2 hL hcL
  have hR' : rightG (x', u) ∈ mixedSet (chartTrace P F f q) :=
    chart_invariant hq m (rightG (x, u)).1 (rightG (x', u)).1 (rightG (x, u)).2 hR hcR
  refine ⟨hL', hR', fun i => ?_⟩
  have hposL := ((mem_mixedSet_near F f _).mp hL).1
  have hposL' := ((mem_mixedSet_near F f _).mp hL').1
  have hdL : ∀ l, ((1 : ℚ) : WithTop ℚ) < ordS ((leftG (x, u)).1 l - (leftG (x', u)).1 l) := fun l =>
    one_lt_ordS_of_cf fun γ hγ => hcL l γ (by rw [lev_self]; exact hγ)
  have hdR : ((1 : ℚ) : WithTop ℚ) < ordS ((rightG (x, u)).1 i - (rightG (x', u)).1 i) :=
    one_lt_ordS_of_cf fun γ hγ => hcR i γ (by rw [lev_self]; exact hγ)
  have hq1 := poly_lipschitz_conc (q i) (fun l => (hposL l).le) (fun l => (hposL' l).le) hdL
  refine one_lt_ordS_of_close (hcl i) ?_
  have he : cev (q i) (leftG (x, u)).1 - (rightG (x, u)).1 i -
      (cev (q i) (leftG (x', u)).1 - (rightG (x', u)).1 i) =
      (cev (q i) (leftG (x, u)).1 - cev (q i) (leftG (x', u)).1) -
        ((rightG (x, u)).1 i - (rightG (x', u)).1 i) := by ring
  rw [he]
  exact one_lt_ordS_sub hq1 hdR

/-! ### (z:coeff:change) for smooth `X` -/

theorem near_covers (m : ℕ+) : Covers m {Fin.elim0} (mixedSet (rawNear F f)) := fun _ _ _ _ =>
  ⟨Fin.elim0, Finset.mem_singleton_self _, fun j => j.elim0⟩

theorem chart_covers (m : ℕ+) : Covers m {Fin.elim0} (mixedSet (chartTrace P F f q)) := fun _ _ _ _ =>
  ⟨Fin.elim0, Finset.mem_singleton_self _, fun j => j.elim0⟩

/-- **The truncations of the chart fibre are the jets of `X`.** `Θ([𝒳_f[m;1]]) = [𝒳_m]`. -/
theorem chart_rawClass (hc : EtaleCoords P F q) (m : ℕ+) :
    rawClass m (bOne m) {Fin.elim0} (strace_definableOver P 0 (milnorDefSetX P F f q))
      (chart_invariant hc.chart m) (chart_covers m) =
      algebraMap EquivariantVariety.ModifiedRing Rloc (jetClassX F f m) := by
  have hq := hc.chart
  have hN := near_invariant F f m
  have hmaps : ∀ p ∈ mixedSet (rawNear F f), RI m p →
      phiQ q p ∈ mixedSet (chartTrace P F f q) ∧ RI m (phiQ q p) := fun p hp hr =>
    ⟨chart_maps hc hp, RI_phiQ (P := P) hc.zero m ((mem_mixedSet_near F f p).mp hp).1 hr⟩
  have e1 := rawClass_eq_of_thickened m (bOne m) (bOne m) {Fin.elim0} {Fin.elim0}
    (rawNear_definableOver F f) (strace_definableOver P 0 (milnorDefSetX P F f q)) hN
    (chart_invariant hq m) (near_covers m) (chart_covers m) (phiQ q) hmaps
    (fun p' hp' hr' => by
      obtain ⟨y, hyr, hypos, hyF, hyf, hyq⟩ := chart_lift hq m p' hp' ⟨fun i => (hr'.1 i).1, hr'.2⟩
      refine ⟨(y, p'.2), (mem_mixedSet_near F f _).mpr ⟨hypos, hyf, fun j => ?_⟩,
        ⟨fun l => ⟨hyr l, isIntegral_of_ordS (hypos l).le⟩, fun j => j.elim0⟩,
        Prod.ext (funext hyq) rfl⟩
      change ((1 : ℚ) : WithTop ℚ) < ordS (cev (F j) y)
      rw [hyF j, ordS_zero]
      exact WithTop.coe_lt_top _)
    (fun p hp p' hp' hr hr' => by
      rw [truncOf_eq_iff m (bOne m) hr hr', truncOf_eq_iff m (bOne m) (hmaps p hp hr).2 (hmaps p' hp' hr').2]
      simp only [lev_self, phiQ]
      rw [and_iff_left (fun j => j.elim0), and_iff_left (fun j => j.elim0)]
      exact chart_resp hc hp hp')
    (rawW P F f q) rawW_definableOver (rawW_invariant hq m)
    (fun p p' hW hr hr' => by
      obtain ⟨hp, hp', hcl⟩ := (mem_rawW p p').mp hW
      refine ⟨hp, hp', ?_⟩
      rw [truncOf_eq_iff m (bOne m) hr' (hmaps p hp hr).2]
      refine ⟨fun i => ?_, fun j => j.elim0⟩
      rw [lev_self]
      change ((1 : ℚ) : WithTop ℚ) < ordS (p'.1 i - cev (q i) p.1)
      rw [← neg_sub, ordS_neg]
      exact hcl i)
    (fun p hp hr => (mem_rawW p (phiQ q p)).mpr ⟨hp, (hmaps p hp hr).1, fun i => by
      change ((1 : ℚ) : WithTop ℚ) < ordS (cev (q i) p.1 - cev (q i) p.1)
      rw [sub_self, ordS_zero]
      exact WithTop.coe_lt_top _⟩)
  rw [← e1]
  apply Linv_cancel (∑ i, bOne (d := N) m i)
  rw [← fullClass_eq_rawClass, fullClass_eq_sum m (bOne m) _ _ _ _ (fun p _ j => j.elim0),
    Finset.sum_singleton]
  rfl

section Final

open SpecialTransformations.Section9
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondSurjectivity
open DiamondIntegral.Section6.DiamondGrothendieck DiamondIntegral.Section6.DiamondLift
open DiamondIntegral.Section7.Theorem726 DiamondIntegral.Section7.DiamondRing DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.BoundedClasses

variable (Gv : Type) [LinearOrderedCommGroupWithZero Gv] [Valued (VF P.N) Gv]
variable (hv : ∀ x y : VF P.N, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hntB : ∃ x : P.G.fieldBase.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

include hntB in
/-- **(z:coeff:change) for a smooth affine `X`**, given étale coordinates at the origin:
`η h_m ∫^◇[𝒳_f] = Θ(𝒳̃_f[m]) = [𝒳_m] [𝔸]^{-m(d+1)}`, where `𝒳_m` is the variety of jets of `X`
(`IsJetX`) and `d + 1 = dim X`. -/
theorem z_coeff_change_smooth (hc : EtaleCoords P F q) (m : ℕ+) :
    PowerSeries.coeff (m : ℕ) (zetaQ P (milnorIntegralX P f Gv hv hntB hc.chart)) =
      algebraMap EquivariantVariety.ModifiedRing Rloc (jetClassX F f m) * Linv ((m : ℕ) * (d + 1)) := by
  have hq := hc.chart
  have e0 := zeta_coeff_of_form_one P Gv hv hntB (milnorObjectX P f hq) (fun p => rfl) m (bOne m)
    {Fin.elim0} (chart_invariant hq m) (chart_covers m) (fun p _ j => j.elim0) (chart_rationalIntegral hq m)
  change PowerSeries.coeff (m : ℕ) (zetaQ P _) = _
  rw [e0, fullClass_eq_rawClass, chart_rawClass hc m]
  congr 2
  simp [bOne, Finset.sum_const, mul_comm]

end Final

end DiamondIntegral.Section8.Truncation
