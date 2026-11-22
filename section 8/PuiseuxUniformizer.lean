import «section 8».GammaHalfspaces
import FubiniTheorems.Comparison.PuiseuxModels.PuiseuxMonsterAmbient

/-! The value of the uniformizer in the Puiseux ambient.

In a Puiseux ambient `P` (an elementary extension `e : Carrier ↪ₑ N` of the concrete model, with
real base the image of `ℂ((t))`), let `π` be the value of the image of `t`. Then

* `uniformizerValue_definable`: `π` is definable over the base `⟨G.real, ∅⟩`;
* `one_lt_uniformizerValue`: `1 < π`;
* `substructureValues_rational`: every value of a nonzero RV element of the substructure generated
  by the base is a rational power `qpow π q`.

These are the three hypotheses of `GammaCells.hasLimit_gamma` for the base of Section 8. The
transfer of values along `e` uses `elementaryGammaTopMap`: the value of the image is the image of
the value. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.PuiseuxValues

open Classical FirstOrder FirstOrder.Language HahnSeries
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.GammaCells

local instance uniformizerSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance uniformizerSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

section transfer

variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF] (e : Carrier ↪ₑ[LRV] N)

theorem vfValue_elementary (a : VFType (M := Carrier)) :
    Values.vfValueHom (elementaryVFFieldHom e a) = elementaryGammaTopMap e (Values.vfValueHom a) := by
  change Values.vrv (CanonicalRV.encodedRv _) = Values.vrv (elementaryRVMap e _)
  rw [elementaryVFFieldHom_rv]

theorem elementaryGammaTopMap_le_iff (x y : Values.GammaTop (M := Carrier)) :
    elementaryGammaTopMap e x ≤ elementaryGammaTopMap e y ↔ x ≤ y := by
  induction x using Quotient.inductionOn with
  | h r =>
    induction y using Quotient.inductionOn with
    | h s =>
      change Values.vrv (elementaryRVMap e r) ≤ Values.vrv (elementaryRVMap e s) ↔
        Values.vrv r ≤ Values.vrv s
      rw [Values.vrv_le_iff, Values.vrv_le_iff]
      exact elementaryRVMap_le e r s

/-- Values in the concrete model are compared through the Puiseux valuation (reversed). -/
theorem vfValue_le_iff (a b : VFType (M := Carrier)) :
    Values.vfValueHom a ≤ Values.vfValueHom b ↔
      puiseuxValuation ℂ (taggedFieldEquiv b) ≤ puiseuxValuation ℂ (taggedFieldEquiv a) := by
  rw [← taggedFieldEquiv_valuation, Values.vf_pred_iff_gamma_le]

theorem ambient_vfValue_eq_of_valuation_eq (u v : Section5.PuiseuxSeries ℂ)
    (h : puiseuxValuation ℂ u = puiseuxValuation ℂ v) :
    Values.vfValueHom (ambientPuiseuxFieldHom e u) = Values.vfValueHom (ambientPuiseuxFieldHom e v) := by
  change Values.vfValueHom (elementaryVFFieldHom e (taggedFieldEquiv.symm u)) =
    Values.vfValueHom (elementaryVFFieldHom e (taggedFieldEquiv.symm v))
  rw [vfValue_elementary, vfValue_elementary]
  congr 1
  apply le_antisymm
  · rw [vfValue_le_iff]; simp [h]
  · rw [vfValue_le_iff]; simp [h]

theorem ambient_vfValue_lt_of_valuation_lt (u v : Section5.PuiseuxSeries ℂ)
    (h : puiseuxValuation ℂ u < puiseuxValuation ℂ v) :
    Values.vfValueHom (ambientPuiseuxFieldHom e v) < Values.vfValueHom (ambientPuiseuxFieldHom e u) := by
  change Values.vfValueHom (elementaryVFFieldHom e (taggedFieldEquiv.symm v)) <
    Values.vfValueHom (elementaryVFFieldHom e (taggedFieldEquiv.symm u))
  rw [vfValue_elementary, vfValue_elementary, lt_iff_le_not_ge, elementaryGammaTopMap_le_iff,
    elementaryGammaTopMap_le_iff, vfValue_le_iff, vfValue_le_iff]
  simp only [RingEquiv.apply_symm_apply]
  exact ⟨h.le, not_le.mpr h⟩

end transfer

/-! ### Orders of Puiseux series -/

/-- The uniformizer `t` as a Puiseux series. -/
def tSeries : Section5.PuiseuxSeries ℂ := (puiseuxBaseUniformizer (k := ℂ) : Section5.PuiseuxSeries ℂ)

theorem tSeries_coe : (tSeries : HahnSeries ℚ ℂ) = single (1 : ℚ) 1 := by
  change (puiseuxRoot (k := ℂ) 1 : HahnSeries ℚ ℂ) = single (1 : ℚ) 1
  norm_num [puiseuxRoot_coe]

theorem tSeries_ne_zero : tSeries ≠ 0 := fun h => by
  have h1 : (tSeries : HahnSeries ℚ ℂ) = 0 := by rw [h]; rfl
  rw [tSeries_coe] at h1
  exact one_ne_zero (single_eq_zero_iff.mp h1)

theorem puiseuxValuation_eq (f : Section5.PuiseuxSeries ℂ) (hf : f ≠ 0) :
    puiseuxValuation ℂ f =
      Multiplicative.ofAdd (OrderDual.toDual (((f : HahnSeries ℚ ℂ).order : ℚ) : WithTop ℚ)) := by
  have hf' : (f : HahnSeries ℚ ℂ) ≠ 0 := fun h => hf (Subtype.ext h)
  change Multiplicative.ofAdd (OrderDual.toDual (HahnSeries.addVal ℚ ℂ (f : HahnSeries ℚ ℂ))) = _
  rw [HahnSeries.addVal_apply, HahnSeries.order_eq_orderTop_of_ne_zero hf']

theorem order_tSeries : ((tSeries : Section5.PuiseuxSeries ℂ) : HahnSeries ℚ ℂ).order = 1 := by
  rw [tSeries_coe, order_single one_ne_zero]

/-- The order of a unit, as a homomorphism to `Multiplicative ℚ`. -/
theorem leadingTerm_fst (u : (Section5.PuiseuxSeries ℂ)ˣ) :
    (puiseuxUnitLeadingTerm u).1 =
      Multiplicative.ofAdd (((u : Section5.PuiseuxSeries ℂ) : HahnSeries ℚ ℂ).order) := rfl

/-- For `f ≠ 0` of order `a / b`, the series `f ^ b · t ^ (−a)` has valuation `1`. -/
theorem valuation_balance (f : Section5.PuiseuxSeries ℂ) (hf : f ≠ 0) :
    puiseuxValuation ℂ
      (f ^ ((f : HahnSeries ℚ ℂ).order.den) *
        tSeries ^ (-((f : HahnSeries ℚ ℂ).order.num))) = 1 := by
  set q := (f : HahnSeries ℚ ℂ).order with hq
  let U : (Section5.PuiseuxSeries ℂ)ˣ := Units.mk0 f hf
  let Ut : (Section5.PuiseuxSeries ℂ)ˣ := Units.mk0 tSeries tSeries_ne_zero
  let V : (Section5.PuiseuxSeries ℂ)ˣ := U ^ q.den * Ut ^ (-q.num)
  have hV : (V : Section5.PuiseuxSeries ℂ) = f ^ q.den * tSeries ^ (-q.num) := by
    simp [V, U, Ut, Units.val_zpow_eq_zpow_val]
  have hord : (((V : Section5.PuiseuxSeries ℂ) : HahnSeries ℚ ℂ).order) = 0 := by
    let ordHom : (Section5.PuiseuxSeries ℂ)ˣ →* Multiplicative ℚ :=
      (MonoidHom.fst (Multiplicative ℚ) ℂˣ).comp puiseuxUnitLeadingTerm
    have hord_apply : ∀ u, ordHom u =
        Multiplicative.ofAdd (((u : Section5.PuiseuxSeries ℂ) : HahnSeries ℚ ℂ).order) := fun _ => rfl
    have h := map_mul ordHom (U ^ q.den) (Ut ^ (-q.num))
    rw [map_pow, map_zpow, hord_apply, hord_apply, hord_apply] at h
    have hU : ((U : Section5.PuiseuxSeries ℂ) : HahnSeries ℚ ℂ).order = q := rfl
    have hUt : ((Ut : Section5.PuiseuxSeries ℂ) : HahnSeries ℚ ℂ).order = 1 := order_tSeries
    rw [hU, hUt, ← ofAdd_nsmul, ← ofAdd_zsmul, ← ofAdd_add] at h
    have h2 : (q.den • q + (-q.num) • (1 : ℚ)) = 0 := by
      rw [nsmul_eq_mul, zsmul_eq_mul, mul_one, Rat.den_mul_eq_num]
      push_cast; ring
    rw [h2, ofAdd_zero] at h
    exact Multiplicative.ofAdd.injective (h.trans ofAdd_zero.symm)
  rw [← hV, puiseuxValuation_eq _ V.ne_zero, hord]
  rfl

/-! ### The uniformizer value in the ambient -/

variable (P : PuiseuxAmbient)

/-- The Laurent field `ℂ((t))` inside the ambient. -/
abbrev laurentField : Subfield (VFType (M := P.N)) := ambientLaurentSubfield P.e

theorem tSeries_mem : ambientPuiseuxFieldHom P.e tSeries ∈ laurentField P :=
  (Subfield.mem_map (f := ambientPuiseuxFieldHom P.e)).mpr
    ⟨tSeries, (puiseuxBaseUniformizer (k := ℂ)).property, rfl⟩

/-- The image of `t` as a unit of the ambient Laurent field. -/
def tUnit : (laurentField P)ˣ :=
  Units.mk0 ⟨ambientPuiseuxFieldHom P.e tSeries, tSeries_mem P⟩ (fun h =>
    (map_ne_zero (ambientPuiseuxFieldHom P.e)).mpr tSeries_ne_zero (congrArg Subtype.val h))

/-- `π`, the value of the uniformizer. -/
def uniformizerValue : Values.Gamma (M := P.N) := vfFieldGammaMap (laurentField P) (tUnit P)

theorem uniformizerValue_val :
    (uniformizerValue P).val = Values.vfValueHom (ambientPuiseuxFieldHom P.e tSeries) := rfl

/-- `π` is definable over the base. -/
theorem uniformizerValue_definable :
    GammaDefinableClosureAtBase ⟨(P.G.real : Set P.N), ∅⟩ (uniformizerValue P) := by
  have h := ambientLaurent_names P.e P.hc (uniformizerValue P) ⟨tUnit P, rfl⟩
  have hcar : (vfFieldSubstructure P.hc (ambientLaurentSubfield P.e) : Set P.N) =
      (P.G.real : Set P.N) := by
    rw [ambientLaurent_carrier P.e P.hc]
    exact P.hB.symm
  rw [hcar] at h
  exact h

theorem one_lt_uniformizerValue : 1 < uniformizerValue P := by
  have hlt : Values.vfValueHom (ambientPuiseuxFieldHom P.e 1) <
      Values.vfValueHom (ambientPuiseuxFieldHom P.e tSeries) := by
    apply ambient_vfValue_lt_of_valuation_lt
    rw [puiseuxValuation_eq _ tSeries_ne_zero, order_tSeries, map_one]
    change Multiplicative.ofAdd (OrderDual.toDual ((1 : ℚ) : WithTop ℚ)) <
      Multiplicative.ofAdd (OrderDual.toDual ((0 : ℚ) : WithTop ℚ))
    rw [Multiplicative.ofAdd_lt, OrderDual.toDual_lt_toDual, WithTop.coe_lt_coe]
    exact one_pos
  rw [map_one, map_one] at hlt
  change (1 : Values.GammaTop (M := P.N)) < (uniformizerValue P).val
  rw [uniformizerValue_val]
  exact hlt

theorem gamma_val_npow (γ : Values.Gamma (M := P.N)) (k : ℕ) : (γ ^ k).val = γ.val ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, Values.gamma_val_mul, ih, pow_succ]

theorem gamma_val_zpow (γ : Values.Gamma (M := P.N)) (k : ℤ) : (γ ^ k).val = γ.val ^ k := by
  cases k with
  | ofNat k => simp only [Int.ofNat_eq_natCast, zpow_natCast, gamma_val_npow]
  | negSucc k => rw [zpow_negSucc, Values.gamma_val_inv, gamma_val_npow, zpow_negSucc]

/-- For `f ≠ 0` of order `a / b`: `v(φ f) ^ b = π ^ a` in the ambient. -/
theorem ambient_value_pow (f : Section5.PuiseuxSeries ℂ) (hf : f ≠ 0) :
    Values.vfValueHom (ambientPuiseuxFieldHom P.e f) ^ ((f : HahnSeries ℚ ℂ).order.den) =
      Values.vfValueHom (ambientPuiseuxFieldHom P.e tSeries) ^ ((f : HahnSeries ℚ ℂ).order.num) := by
  have h := ambient_vfValue_eq_of_valuation_eq P.e _ 1
    ((valuation_balance f hf).trans (map_one _).symm)
  rw [map_one, map_one, map_mul, map_pow, map_zpow₀, map_mul, map_pow, map_zpow₀] at h
  have ht0 : Values.vfValueHom (ambientPuiseuxFieldHom P.e tSeries) ≠ 0 :=
    (map_ne_zero _).mpr ((map_ne_zero _).mpr tSeries_ne_zero)
  rw [zpow_neg, mul_inv_eq_one₀ (zpow_ne_zero _ ht0)] at h
  exact h

/-- A value of a nonzero element of `ℂ((t))` is a rational power of `π`. -/
theorem gamma_of_ambient (f : Section5.PuiseuxSeries ℂ) (hf : f ≠ 0) (δ : Values.Gamma (M := P.N))
    (hδ : δ.val = Values.vfValueHom (ambientPuiseuxFieldHom P.e f)) :
    δ = qpow (uniformizerValue P) ((f : HahnSeries ℚ ℂ).order) := by
  set q := (f : HahnSeries ℚ ℂ).order
  apply HasUniqueRoots.pow_left_injective q.den_ne_zero
  change δ ^ q.den = qpow (uniformizerValue P) q ^ q.den
  rw [qpow_pow_den]
  apply Subtype.ext
  rw [gamma_val_npow, gamma_val_zpow, hδ, uniformizerValue_val]
  exact ambient_value_pow P f hf

/-- **The base values are rational powers of `π`.** -/
theorem substructureValues_rational :
    ∀ δ ∈ Section2.GammaStable.substructureValues
        (Substructure.closure LRV (P.G.real : Set P.N)),
      ∃ q : ℚ, δ = qpow (uniformizerValue P) q := by
  rintro δ ⟨c, hcK, hc0, hcδ⟩
  rw [Substructure.closure_eq] at hcK
  have hcar : c.val ∈ (vfFieldSubstructure P.hc (ambientLaurentSubfield P.e) : Set P.N) := by
    rw [ambientLaurent_carrier P.e P.hc]
    have := P.hB
    simp only [GammaGroundContext.base] at this
    rw [← this]
    exact hcK
  obtain ⟨x, hx, hxc⟩ := (vfFieldCarrier_rv _ c).mp hcar
  obtain ⟨f, -, rfl⟩ := (Subfield.mem_map (f := ambientPuiseuxFieldHom P.e)).mp hx
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hc0
    rw [← hxc, map_zero]
    exact (ValuedModelMap.encodedRv_zero (M := P.N)).trans (Subtype.ext RVOperations.zero_val.symm)
  refine ⟨(f : HahnSeries ℚ ℂ).order, gamma_of_ambient P f hf0 δ ?_⟩
  rw [← hcδ, ← hxc]
  rfl

open DiamondIntegral.Section4 GammaOrderLogic in
/-- **Lemma 8.9 in the Puiseux ambient.** Let `X ⊆ Γⁿ` be definable over the base `⟨G.real, ∅⟩`,
doubly bounded by powers of `π`, and covered by finitely many definable pieces on whose rational
traces the weight is integral affine. Then the lattice-point series of the rational trace of `X`
lies in `R[T]†`, has degree `≤ 0`, and its limit is `−χ(X)`, the geometric Euler characteristic of
the library. -/
theorem lemma_8_9 {n : ℕ} (X : Set (Fin n → Values.Gamma (M := P.N)))
    (hX : GammaDefinable ⟨(P.G.real : Set P.N), ∅⟩ X) (N : ℕ)
    (hbd : ∀ z ∈ X, ∀ i, uniformizerValue P ^ (-(N : ℤ)) ≤ z i ∧ z i ≤ uniformizerValue P ^ (N : ℤ))
    {ρ : Type} [Fintype ρ] (Pc : ρ → Set (Fin n → Values.Gamma (M := P.N)))
    (hP : ∀ r, GammaDefinable ⟨(P.G.real : Set P.N), ∅⟩ (Pc r))
    (hcov : X ⊆ ⋃ r, Pc r) (a : ρ → Fin n → ℤ) (b : ρ → ℤ) (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (r : ρ) (x : Fin n → ℤ) (m : ℕ),
      (fun i => (x i : ℚ) / m) ∈ ratTrace (uniformizerValue P) X ∩
        ratTrace (uniformizerValue P) (Pc r) → wt x m = ∑ i, a r i * x i + b r * m)
    {R : Type*} [CommRing R] (A : Rˣ) :
    RationalSeries.HasLimit A
      (SimplexSeries.latticeSeries A (ratTrace (uniformizerValue P) X) wt)
      (-((GammaIteratedIntegral.integrateAll P.G.model00 P.G.uncountable.le P.G.saturated
        ⟨(P.G.real : Set P.N), ∅⟩ P.G.small_real
        (by simpa using Cardinal.aleph0_pos.trans P.G.uncountable) EulerKind.geometric n
          (GammaIndicators.indicatorFamily ⟨(P.G.real : Set P.N), ∅⟩ X hX) : ℤ) : R)) :=
  hasLimit_gamma P.hc P.G.model00 P.G.uncountable P.G.saturated P.G.homogeneous
    (P.G.real : Set P.N) P.G.small_real (one_lt_uniformizerValue P)
    (uniformizerValue_definable P) (substructureValues_rational P) X hX N hbd Pc hP hcov a b wt
    hwt A

end DiamondIntegral.Section8.PuiseuxValues
