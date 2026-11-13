import «section 4».GammaNamesSubgroup
import Section3.GammaDefinableClosureField
import Section3.GammaFullDescent
import Section3.RVOperations

/-! Original-base definable RV lifts, as accepted for Notation 4.13.
Their values form a subgroup of the definable Gamma constants. No
divisibility or choice of an RV section is asserted for this subgroup. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaRVLifts

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rvNames (B : Base (M := M)) : Subgroup (CanonicalRV.RVSort M)ˣ where
  carrier := {t | DefinableClosureAtBase B .rv (t.val).val}
  one_mem' := by
    change DefinableClosureAtBase B .rv (1 : CanonicalRV.RVSort M).val
    rw [RVOperations.one_val]
    exact definableClosureAtBase_function_symbol B Fn.rvOne Fin.elim0
      (fun i => i.elim0) (fun i => i.elim0)
  mul_mem' := by
    intro t u ht hu
    change DefinableClosureAtBase B .rv (t.val * u.val).val
    rw [RVOperations.mul_val]
    exact definableClosureAtBase_function_symbol B Fn.rvMul ![t.val.val, u.val.val]
      (by intro i; fin_cases i; exact t.val.property; exact u.val.property)
      (by intro i; fin_cases i; exact ht; exact hu)
  inv_mem' := by
    intro t ht
    change DefinableClosureAtBase B .rv (↑(t⁻¹) : CanonicalRV.RVSort M).val
    rw [Units.val_inv_eq_inv_val, RVOperations.inv_val]
    exact definableClosureAtBase_function_symbol B Fn.rvInv ![t.val.val]
      (by intro i; fin_cases i; exact t.val.property)
      (by intro i; fin_cases i; exact ht)

theorem unit_nonzero_code (t : (CanonicalRV.RVSort M)ˣ) : NonzeroRV t.val.val := by
  refine ⟨t.val.property, ?_⟩
  intro h
  exact Units.ne_zero t (Subtype.ext (h.trans RVOperations.zero_val.symm))

def valueHom : (CanonicalRV.RVSort M)ˣ →* Values.Gamma (M := M) where
  toFun t := codeValue t.val.val
  map_one' := by
    let c : Code (M := M) := ⟨1, (unit_nonzero_code 1).2⟩
    change codeValue (1 : CanonicalRV.RVSort M).val = 1
    exact (codeValue_raw c).trans (Subtype.ext RVOperations.vrv_one)
  map_mul' t u := by
    change codeValue (t.val * u.val).val = codeValue t.val.val * codeValue u.val.val
    rw [RVOperations.mul_val]
    exact GammaGroupNames.codeValue_mul _ _ (unit_nonzero_code t) (unit_nonzero_code u)

def liftableValues (B : Base (M := M)) : Subgroup (Values.Gamma (M := M)) :=
  (rvNames B).map valueHom

theorem mem_liftableValues_iff (B : Base (M := M)) (γ : Values.Gamma (M := M)) :
    γ ∈ liftableValues B ↔ ∃ t : Code (M := M), DefinableClosureAtBase B .rv (raw t) ∧ value t = γ := by
  constructor
  · rintro ⟨t, ht, hγ⟩
    let c : Code (M := M) := ⟨t.val, (unit_nonzero_code t).2⟩
    refine ⟨c, ht, ?_⟩
    exact (codeValue_raw c).symm.trans hγ
  · rintro ⟨t, ht, hγ⟩
    have ht0 : t.val ≠ (0 : CanonicalRV.RVSort M) := by
      intro h
      exact t.property ((congrArg Subtype.val h).trans RVOperations.zero_val)
    refine ⟨Units.mk0 t.val ht0, ht, ?_⟩
    exact (codeValue_raw t).trans hγ

theorem liftableValues_le_names (B : Base (M := M)) :
    liftableValues B ≤ GammaNamesSubgroup.namesSubgroup B := by
  intro γ hγ
  obtain ⟨t, ht, rfl⟩ := (mem_liftableValues_iff B γ).mp hγ
  have h := gamma_value_of_named_code (closureBase B) t ⟨.rv, ht⟩
  exact (DefinableAtBase.closureBase_iff B .rv (Values.gammaPullback {value t})).mp h

def admissibleRadii (B : Base (M := M)) : Set (Values.Gamma (M := M)) :=
  {γ | 1 ≤ γ ∧ γ ∈ liftableValues B}

theorem admissibleRadii_iff (B : Base (M := M)) (γ : Values.Gamma (M := M)) :
    γ ∈ admissibleRadii B ↔ 1 ≤ γ ∧
      ∃ t : Code (M := M), DefinableClosureAtBase B .rv (raw t) ∧ value t = γ :=
  and_congr_right (fun _ => mem_liftableValues_iff B γ)

theorem one_admissible (B : Base (M := M)) : 1 ∈ admissibleRadii B :=
  ⟨le_rfl, (liftableValues B).one_mem⟩

theorem mul_admissible (B : Base (M := M)) {γ δ : Values.Gamma (M := M)}
    (hγ : γ ∈ admissibleRadii B) (hδ : δ ∈ admissibleRadii B) : γ * δ ∈ admissibleRadii B :=
  ⟨one_le_mul hγ.1 hδ.1, (liftableValues B).mul_mem hγ.2 hδ.2⟩

theorem admissible_definable (B : Base (M := M)) {γ : Values.Gamma (M := M)}
    (hγ : γ ∈ admissibleRadii B) : GammaDefinableClosureAtBase B γ :=
  liftableValues_le_names B hγ.2

end DiamondIntegral.Section4.GammaRVLifts
