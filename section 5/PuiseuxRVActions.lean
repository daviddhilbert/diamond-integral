import «section 5».PuiseuxRV
import «section 5».ValuedRVActions
import «section 5».RationalRVAutomorphisms

/-! The actual quotient RV action and lifting of all multiplicative RV
automorphisms fixing the integral-value/constant base. The separate bridge
to the paper's induced original-language structure remains explicit. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open HahnSeries
variable {k : Type*} [Field k]

theorem puiseuxRVUnitEquiv_mk (u : (PuiseuxSeries k)ˣ) :
    puiseuxRVUnitEquiv (QuotientGroup.mk' (RVCalc.principalUnits (puiseuxValuation k)) u) =
      puiseuxUnitLeadingTerm u := rfl

section AlgebraicallyClosed
variable [CharZero k] [IsAlgClosed k]

theorem puiseuxAutomorphism_valuation
    (σ : PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k) (f : PuiseuxSeries k) :
    puiseuxValuation k (σ f) = puiseuxValuation k f :=
  puiseuxAutomorphism_orderTop σ f

/-- The actual action on the principal-unit quotient. -/
def puiseuxRVAction (σ : PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k) :
    RVCalc.RVUnit (puiseuxValuation k) ≃* RVCalc.RVUnit (puiseuxValuation k) :=
  valuedRVUnitEquiv (puiseuxValuation k) σ.toRingEquiv (puiseuxAutomorphism_valuation σ)

theorem puiseuxRVAction_rootSystem_mk (η : CompatibleRoots k) (u : (PuiseuxSeries k)ˣ) :
    puiseuxRVUnitEquiv (puiseuxRVAction (puiseuxRootSystemAction η)
      (QuotientGroup.mk' (RVCalc.principalUnits (puiseuxValuation k)) u)) =
    ((puiseuxUnitLeadingTerm u).1,
      compatibleRootCharacter η (puiseuxUnitLeadingTerm u).1 * (puiseuxUnitLeadingTerm u).2) := by
  let σ := puiseuxRootSystemAction η
  let w := Units.mapEquiv σ.toRingEquiv.toMulEquiv u
  have horder : ((w : PuiseuxSeries k) : HahnSeries ℚ k).order =
      ((u : PuiseuxSeries k) : HahnSeries ℚ k).order := by
    have ho := puiseuxRootSystemAction_orderTop η (u : PuiseuxSeries k)
    change ((w : PuiseuxSeries k) : HahnSeries ℚ k).orderTop =
      ((u : PuiseuxSeries k) : HahnSeries ℚ k).orderTop at ho
    rw [← order_eq_orderTop_of_ne_zero (puiseuxUnit_coe_ne_zero w),
      ← order_eq_orderTop_of_ne_zero (puiseuxUnit_coe_ne_zero u)] at ho
    exact WithTop.coe_injective ho
  change puiseuxUnitLeadingTerm w = _
  apply Prod.ext
  · change Multiplicative.ofAdd ((w : PuiseuxSeries k) : HahnSeries ℚ k).order = _
    rw [horder]
    rfl
  · apply Units.ext
    change ((w : PuiseuxSeries k) : HahnSeries ℚ k).leadingCoeff =
      (compatibleRootCharacter η
        (Multiplicative.ofAdd ((u : PuiseuxSeries k) : HahnSeries ℚ k).order) : k) *
        ((u : PuiseuxSeries k) : HahnSeries ℚ k).leadingCoeff
    rw [leadingCoeff_eq, horder, leadingCoeff_eq]
    exact hahnCharacterEquiv_coeff (compatibleRootCharacter η)
      ((u : PuiseuxSeries k) : HahnSeries ℚ k) _

/-- This is the intrinsic form of c*r_n^a |-> c*eta_n^a*r_n^a. -/
theorem puiseuxRVAction_coordinates (η : CompatibleRoots k)
    (r : RVCalc.RVUnit (puiseuxValuation k)) :
    puiseuxRVUnitEquiv (puiseuxRVAction (puiseuxRootSystemAction η) r) =
      ((puiseuxRVUnitEquiv r).1,
        compatibleRootCharacter η (puiseuxRVUnitEquiv r).1 * (puiseuxRVUnitEquiv r).2) := by
  induction r using Quotient.inductionOn' with
  | h u => exact puiseuxRVAction_rootSystem_mk η u

/-- Every group automorphism of actual RV units fixing integral-value
constants lifts to an actual Laurent-base field automorphism. -/
theorem puiseuxRVAutomorphism_lifts
    (ψ : RVCalc.RVUnit (puiseuxValuation k) ≃* RVCalc.RVUnit (puiseuxValuation k))
    (hfix : ∀ (z : ℤ) (c : kˣ), ψ ((puiseuxRVUnitEquiv (k := k)).symm
      (Multiplicative.ofAdd (z : ℚ), c)) =
        (puiseuxRVUnitEquiv (k := k)).symm (Multiplicative.ofAdd (z : ℚ), c)) :
    ∃ η : CompatibleRoots k, puiseuxRVAction (puiseuxRootSystemAction η) = ψ := by
  let e := puiseuxRVUnitEquiv (k := k)
  let φ := (e.symm.trans ψ).trans e
  have hφ : ∀ (z : ℤ) (c : kˣ), φ (Multiplicative.ofAdd (z : ℚ), c) =
      (Multiplicative.ofAdd (z : ℚ), c) := by
    intro z c
    change e (ψ (e.symm (Multiplicative.ofAdd (z : ℚ), c))) = _
    rw [hfix, e.apply_symm_apply]
  obtain ⟨η, hη⟩ := rationalRVAutomorphism_system φ hφ
  refine ⟨η, ?_⟩
  apply MulEquiv.ext
  intro r
  apply e.injective
  rw [puiseuxRVAction_coordinates]
  have hh := hη (e r).1.toAdd (e r).2
  change e (ψ (e.symm (e r))) = _ at hh
  rw [e.symm_apply_apply] at hh
  exact hh.symm

/-- Distinct compatible systems already give distinct actual RV actions. -/
theorem puiseuxRVRootSystemAction_injective :
    Function.Injective (fun η : CompatibleRoots k => puiseuxRVAction (puiseuxRootSystemAction η)) := by
  intro η θ h
  apply rationalRVSystem_unique
  intro q
  let e := puiseuxRVUnitEquiv (k := k)
  have hh := congrArg (fun ψ : RVCalc.RVUnit (puiseuxValuation k) ≃*
      RVCalc.RVUnit (puiseuxValuation k) => e (ψ (e.symm (Multiplicative.ofAdd q, 1)))) h
  rw [puiseuxRVAction_coordinates, puiseuxRVAction_coordinates, e.apply_symm_apply] at hh
  simpa using congrArg Prod.snd hh

/-- Faithfulness for the full field-automorphism group, not just chosen actions. -/
theorem puiseuxRVAction_injective : Function.Injective (puiseuxRVAction (k := k)) := by
  intro σ τ h
  rw [← puiseuxRootSystemAction_system σ, ← puiseuxRootSystemAction_system τ] at h ⊢
  exact congrArg puiseuxRootSystemAction (puiseuxRVRootSystemAction_injective h)

def puiseuxRVBaseAutomorphisms (k : Type*) [Field k] :
    Subgroup (RVCalc.RVUnit (puiseuxValuation k) ≃* RVCalc.RVUnit (puiseuxValuation k)) where
  carrier := {ψ | ∀ (z : ℤ) (c : kˣ), ψ ((puiseuxRVUnitEquiv (k := k)).symm
    (Multiplicative.ofAdd (z : ℚ), c)) =
      (puiseuxRVUnitEquiv (k := k)).symm (Multiplicative.ofAdd (z : ℚ), c)}
  one_mem' := by intro z c; rfl
  mul_mem' := by
    intro ψ φ hψ hφ z c
    change ψ (φ _) = _
    rw [hφ, hψ]
  inv_mem' := by
    intro ψ hψ z c
    apply ψ.injective
    change ψ (ψ.symm _) = ψ _
    rw [ψ.apply_symm_apply, hψ]

theorem puiseuxRVAction_fixes_base
    (σ : PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k) :
    puiseuxRVAction σ ∈ puiseuxRVBaseAutomorphisms k := by
  intro z c
  rw [← puiseuxRootSystemAction_system σ]
  apply (puiseuxRVUnitEquiv (k := k)).injective
  rw [puiseuxRVAction_coordinates, MulEquiv.apply_symm_apply,
    compatibleRootCharacter_int, one_mul]

def puiseuxRVActionHom : (PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k) →*
    puiseuxRVBaseAutomorphisms k where
  toFun σ := ⟨puiseuxRVAction σ, puiseuxRVAction_fixes_base σ⟩
  map_one' := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro r
    induction r using Quotient.inductionOn' with
    | h u => rfl
  map_mul' σ τ := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro r
    induction r using Quotient.inductionOn' with
    | h u => rfl

/-- The actual quotient RV group gives the same Galois group over integral
values and constants. Identifying its full induced language remains a bridge. -/
def puiseuxRVGaloisEquiv :
    (PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k) ≃*
      puiseuxRVBaseAutomorphisms k :=
  MulEquiv.ofBijective (puiseuxRVActionHom (k := k)) (by
    constructor
    · intro σ τ h
      exact puiseuxRVAction_injective (congrArg Subtype.val h)
    · intro ψ
      obtain ⟨η, hη⟩ := puiseuxRVAutomorphism_lifts ψ.val ψ.property
      exact ⟨puiseuxRootSystemAction η, Subtype.ext hη⟩)

/-- The finite-level monodromy formula for arbitrary integral powers. -/
theorem puiseuxRVAction_fraction (η : CompatibleRoots k) (n : ℕ+) (a : ℤ) (c : kˣ) :
    puiseuxRVUnitEquiv (puiseuxRVAction (puiseuxRootSystemAction η)
      ((puiseuxRVUnitEquiv (k := k)).symm
        (Multiplicative.ofAdd ((a : ℚ) / (n : ℕ)), c))) =
      (Multiplicative.ofAdd ((a : ℚ) / (n : ℕ)), η.val n ^ a * c) := by
  rw [puiseuxRVAction_coordinates, MulEquiv.apply_symm_apply, compatibleRootCharacter_fraction]

end AlgebraicallyClosed

/-- The concrete complex-field quotient RV identification in Remark 5.13. -/
def complexPuiseuxRVGaloisEquiv :
    (PuiseuxSeries ℂ ≃ₐ[puiseuxBaseSubfield ℂ] PuiseuxSeries ℂ) ≃*
      puiseuxRVBaseAutomorphisms ℂ := puiseuxRVGaloisEquiv

end DiamondIntegral.Section5
