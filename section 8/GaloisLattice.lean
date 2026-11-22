import «section 8».PuiseuxBase
import FubiniTheorems.Comparison.PuiseuxModels.PuiseuxDefinableMaps
import HilbertMathlib.Foundation.Series.FiniteRootProjection

/-! The Galois action on the concrete model and the lattice `m⁻¹ℤ`.

The concrete model is `Carrier = ℂ{{t}} ⊕ RV`, with `RV = Option (ℚ × ℂˣ)`; the nonzero RV element
`(q, c)` is `rv(c t^q)`. A compatible system of roots of unity `η` acts on `Carrier` fixing
`ℂ((t))` and sends `(q, c)` to `(q, χ_η(q) c)`.

* `levelRoots m = W ^ m`, `W` the winding system (`W(n) = e^{2πi/n}`): its character is trivial
  exactly on `m⁻¹ℤ` (`char_levelRoots_eq_one_iff`). So the action of `levelRoots m` fixes the RV
  elements with value in `m⁻¹ℤ` and moves every other nonzero RV element.
* `codeValue_rv_some`: in a Puiseux ambient `P`, the image of `(q, c)` has value `π^q`, and the
  image of the RV zero has `codeValue` `1`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Galois

open Classical FirstOrder FirstOrder.Language HahnSeries
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.GammaCells DiamondIntegral.Section8.PuiseuxValues

local instance galoisSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance galoisSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

/-! ### Roots of unity of level `m` -/

/-- The compatible root system `W ^ m`. -/
def levelRoots (m : ℕ+) : CompatibleRoots ℂ := windingRootSystem ^ (m : ℕ)

theorem levelRoots_apply (m n : ℕ+) :
    (levelRoots m).val n = windingRootSystem.val n ^ (m : ℕ) := rfl

theorem levelRoots_level (m : ℕ+) : (levelRoots m).val m = 1 := by
  rw [levelRoots_apply]; exact windingRootSystem.property.1 m

theorem char_levelRoots (m : ℕ+) (q : ℚ) :
    ((compatibleRootCharacter (levelRoots m) (Multiplicative.ofAdd q) : ℂˣ) : ℂ) =
      ((windingRootSystem.val ⟨q.den, q.den_pos⟩ : ℂˣ) : ℂ) ^ ((m : ℤ) * q.num) := by
  change ((((levelRoots m).val ⟨q.den, q.den_pos⟩) ^ q.num : ℂˣ) : ℂ) = _
  rw [levelRoots_apply, ← zpow_natCast, ← zpow_mul, Units.val_zpow_eq_zpow_val]

theorem char_levelRoots_eq_one_iff (m : ℕ+) (q : ℚ) :
    compatibleRootCharacter (levelRoots m) (Multiplicative.ofAdd q) = 1 ↔
      ∃ z : ℤ, q = (z : ℚ) / (m : ℕ) := by
  have hprim := windingRootSystem_primitive ⟨q.den, q.den_pos⟩
  rw [← Units.val_eq_one, char_levelRoots, hprim.zpow_eq_one_iff_dvd]
  change ((q.den : ℕ) : ℤ) ∣ (m : ℤ) * q.num ↔ _
  have hcop : IsCoprime ((q.den : ℕ) : ℤ) q.num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact_mod_cast q.reduced
  rw [show ((q.den : ℕ) : ℤ) ∣ (m : ℤ) * q.num ↔ ((q.den : ℕ) : ℤ) ∣ (m : ℤ) from
    ⟨hcop.dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h _⟩]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨q.num * c, ?_⟩
    have hm : ((m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr m.ne_zero
    have hc' : ((m : ℕ) : ℚ) = q.den * c := by exact_mod_cast hc
    rw [eq_div_iff hm, hc', ← mul_assoc, Rat.mul_den_eq_num]
    push_cast
    ring
  · rintro ⟨z, hz⟩
    have hm : ((m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr m.ne_zero
    have h1 : q * (m : ℕ) = z := by rw [hz]; field_simp
    have h2 : (q * q.den) * (m : ℕ) = z * q.den := by rw [mul_right_comm, h1]
    rw [Rat.mul_den_eq_num] at h2
    have h3 : q.num * ((m : ℕ) : ℤ) = z * q.den := by exact_mod_cast h2
    exact hcop.dvd_of_dvd_mul_left ⟨z, by rw [h3]; ring⟩

/-! ### The action on RV elements -/

theorem rvAction_some (η : CompatibleRoots ℂ) (u : RationalRVUnits ℂ) :
    rvAction η (some u) = some (u.1, compatibleRootCharacter η u.1 * u.2) := rfl

theorem rvAction_none (η : CompatibleRoots ℂ) : rvAction η none = none := rfl

theorem carrierAction_inr (η : CompatibleRoots ℂ) (r : RV) :
    carrierAction η (Sum.inr r) = Sum.inr (rvAction η r) := rfl

/-- `levelRoots m` fixes `(q, c)` exactly when `q ∈ m⁻¹ℤ`. -/
theorem levelRoots_fixes_iff (m : ℕ+) (u : RationalRVUnits ℂ) :
    rvAction (levelRoots m) (some u) = some u ↔ ∃ z : ℤ, u.1.toAdd = (z : ℚ) / (m : ℕ) := by
  rw [rvAction_some, ← char_levelRoots_eq_one_iff, ofAdd_toAdd]
  constructor
  · intro h
    have h2 := congrArg (fun r : RV => r.map Prod.snd) h
    simp only [Option.map_some] at h2
    have h3 := Option.some_injective _ h2
    exact mul_right_cancel (a := compatibleRootCharacter (levelRoots m) u.1) (b := u.2) (c := 1)
      (by rw [one_mul]; exact h3)
  · intro h
    rw [h, one_mul]

/-! ### Values of concrete RV elements in the ambient -/

variable (P : PuiseuxAmbient)

local notation "π" => uniformizerValue P

theorem exists_rvOfField (u : RationalRVUnits ℂ) :
    ∃ f : Section5.PuiseuxSeries ℂ, f ≠ 0 ∧ rvOfField f = some u ∧
      (f : HahnSeries ℚ ℂ).order = u.1.toAdd := by
  obtain ⟨U, hU⟩ := QuotientGroup.mk'_surjective (RVCalc.principalUnits (puiseuxValuation ℂ))
    ((puiseuxRVUnitEquiv (k := ℂ)).symm u)
  have hf : (U : Section5.PuiseuxSeries ℂ) ≠ 0 := U.ne_zero
  have hrv : rvOfField (U : Section5.PuiseuxSeries ℂ) = some u := by
    rw [rvOfField, RVCalc.rv_of_ne hf]
    have hu : Units.mk0 (U : Section5.PuiseuxSeries ℂ) hf = U := Units.ext rfl
    change some (puiseuxRVUnitEquiv (QuotientGroup.mk' _ (Units.mk0 _ hf))) = _
    rw [hu, hU, MulEquiv.apply_symm_apply]
  refine ⟨U, hf, hrv, ?_⟩
  have h := congrArg Prod.fst (puiseuxRVUnitEquiv_mk (k := ℂ) U)
  rw [hU, MulEquiv.apply_symm_apply] at h
  rw [h]
  rfl

theorem codeValue_encodedRv (y : VFType (M := P.N)) (hy : y ≠ 0) :
    (codeValue ((CanonicalRV.encodedRv y).val)).val = Values.vfValueHom y := by
  have h0 : NonzeroRV (CanonicalRV.encodedRv y).val :=
    ⟨(CanonicalRV.encodedRv y).property, fun h => hy ((CanonicalRV.encodedRv_zero_iff y).mp h)⟩
  simp only [codeValue, h0, ↓reduceDIte]
  rfl

theorem codeValue_rvOfField (f : Section5.PuiseuxSeries ℂ) (hf : f ≠ 0) :
    codeValue (P.e (Sum.inr (rvOfField f))) = qpow π ((f : HahnSeries ℚ ℂ).order) := by
  rw [← ambientPuiseux_rv_val P.e f]
  have hy : ambientPuiseuxFieldHom P.e f ≠ 0 :=
    (map_ne_zero (ambientPuiseuxFieldHom P.e)).mpr hf
  exact gamma_of_ambient P f hf _ (codeValue_encodedRv P _ hy)

/-- The image of the RV element `(q, c)` has value `π^q`. -/
theorem codeValue_rv_some (u : RationalRVUnits ℂ) :
    codeValue (P.e (Sum.inr (some u))) = qpow π u.1.toAdd := by
  obtain ⟨f, hf, hrv, hord⟩ := exists_rvOfField u
  rw [← hrv, codeValue_rvOfField P f hf, hord]

/-- The image of the RV zero has `codeValue` `1`. -/
theorem codeValue_rv_none : codeValue (P.e (Sum.inr (none : RV))) = 1 := by
  have h := ambientPuiseux_rv_val P.e 0
  rw [rvOfField_zero, map_zero] at h
  rw [← h]
  have hz : ¬ NonzeroRV (CanonicalRV.encodedRv (0 : VFType (M := P.N))).val := fun h0 =>
    h0.2 ((CanonicalRV.encodedRv_zero_iff (0 : VFType (M := P.N))).mpr rfl)
  simp only [codeValue, hz, ↓reduceDIte]

/-- The image of the RV element `(q, c)` is in the lattice at level `m` exactly when the action
of `levelRoots m` fixes it. -/
theorem inLattice_iff_fixed (m : ℕ+) (u : RationalRVUnits ℂ) :
    InLattice π m (codeValue (P.e (Sum.inr (some u)))) ↔
      rvAction (levelRoots m) (some u) = some u := by
  rw [codeValue_rv_some, levelRoots_fixes_iff]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := eq_qpow_of_inLattice m.ne_zero h
    exact ⟨z, qpow_injective (one_lt_uniformizerValue P) hz⟩
  · rintro ⟨z, hz⟩
    rw [hz]
    exact inLattice_qpow _ z m.ne_zero

end DiamondIntegral.Section8.Galois
