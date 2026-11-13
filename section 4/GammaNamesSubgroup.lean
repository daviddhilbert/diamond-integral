import «section 4».GammaGroupNames
import «section 4».GammaRelationLogic

/-! The actual definable Gamma constants form a group over the original
base. This gives the precise index group of the degree-zero group ring. -/

set_option autoImplicit false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaNamesSubgroup
open GammaOrderLogic GammaDefinableEuler GammaGroupNames

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem inverse_definable_base (B : Base (M := M)) (a : Values.Gamma (M := M))
    (ha : GammaDefinableClosureAtBase B a) : GammaDefinableClosureAtBase B a⁻¹ := by
  have ha1 := (unary_definable_iff B {a}).mpr ha
  have ho1 := (unary_definable_iff B {1}).mpr (one_definable_base B)
  have ha3 := GammaRelationLogic.preimage_definable_base B _ ha1
    (fun _ : Fin 1 => (0 : Fin 3))
  have ho3 := GammaRelationLogic.preimage_definable_base B _ ho1
    (fun _ : Fin 1 => (1 : Fin 3))
  have hg3 := GammaRelationLogic.preimage_definable_base B _ (mul_graph_definable_base B)
    (![0, 2, 1] : Fin 3 → Fin 3)
  have hP : GammaDefinable B {z : Fin 3 → Values.Gamma (M := M) |
      z 0 = a ∧ z 1 = 1 ∧ z 0 * z 2 = z 1} := by
    have h := GammaRelationLogic.inter_definable_base B _ _
      (GammaRelationLogic.inter_definable_base B _ _ ha3 ho3) hg3
    convert h using 1
    ext z
    change (z 0 = a ∧ z 1 = 1 ∧ z 0 * z 2 = z 1) ↔
      ((z 0 = a ∧ z 1 = 1) ∧ z 0 * z 2 = z 1)
    tauto
  have hQ := GammaRelationLogic.exists_definable_base B _
    (GammaRelationLogic.exists_definable_base B _ hP)
  change GammaDefinable B {z : Fin 1 → Values.Gamma (M := M) |
    ∃ u v, v = a ∧ u = 1 ∧ v * z 0 = u} at hQ
  have he : {z : Fin 1 → Values.Gamma (M := M) | ∃ u v, v = a ∧ u = 1 ∧ v * z 0 = u} =
      {z | z 0 = a⁻¹} := by
    ext z
    constructor
    · rintro ⟨u, v, hv, hu, h⟩
      rw [hv, hu] at h
      apply mul_left_cancel (a := a)
      rw [h, mul_inv_cancel]
    · intro h
      exact ⟨1, a, rfl, rfl, by rw [h, mul_inv_cancel]⟩
  apply (unary_definable_iff B {a⁻¹}).mp
  rwa [he] at hQ

def namesSubgroup (B : Base (M := M)) : Subgroup (Values.Gamma (M := M)) where
  carrier := {a | GammaDefinableClosureAtBase B a}
  one_mem' := one_definable_base B
  mul_mem' := fun ha hb => mul_definable_base B _ _ ha hb
  inv_mem' := fun ha => inverse_definable_base B _ ha

def additiveNames (B : Base (M := M)) : AddSubgroup (PaperGamma (M := M)) where
  carrier := {a | GammaDefinableClosureAtBase B (toPaperGamma.symm a)}
  zero_mem' := zero_definable_base B
  add_mem' := fun ha hb => add_definable_base B _ _ ha hb
  neg_mem' := fun ha => inverse_definable_base B _ ha

abbrev DefinableGammaGroupRing (B : Base (M := M)) := AddMonoidAlgebra ℤ (additiveNames B)

end DiamondIntegral.Section4.GammaNamesSubgroup
