import «section 4».GammaPartialCellDefinability
import «section 4».GammaFamilyBoundary

/-! Definable base sets selecting nonempty boundary-free fibre shapes.
Only Gamma coordinate projection is used. No endpoint representatives or
choice of a point in each nonempty fibre is made. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundaryStackBases
open GammaOrderLogic GammaCellSections GammaCellUnboundedSections GammaPartialCellDefinability
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def fibreBase {n : ℕ} (S : Set (Fin (n + 1) → Values.Gamma (M := M))) :
    Set (Fin n → Values.Gamma (M := M)) := (fun z => Fin.tail z) '' S

theorem mem_fibreBase {n : ℕ} (S : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (y : Fin n → Values.Gamma (M := M)) : y ∈ fibreBase S ↔ ∃ x, Fin.cons x y ∈ S := by
  constructor
  · rintro ⟨z, hz, he⟩
    refine ⟨z 0, ?_⟩
    rw [← he, Fin.cons_self_tail]
    exact hz
  · rintro ⟨x, hx⟩
    exact ⟨Fin.cons x y, hx, rfl⟩

theorem fibreBase_definable (B : Base (M := M)) {n : ℕ}
    (S : Set (Fin (n + 1) → Values.Gamma (M := M))) (hS : GammaDefinable B S) :
    GammaDefinable B (fibreBase S) :=
  GammaQuantifierLogic.image_definable_base B S hS Fin.succ (Fin.succ_injective n)

def activeBase {n : ℕ} (R S : Set (Fin (n + 1) → Values.Gamma (M := M))) :
    Set (Fin n → Values.Gamma (M := M)) :=
  fibreBase (R ∩ S) ∩ (fibreBase (GammaFamilyBoundary.Boundary R ∩ S))ᶜ

theorem mem_activeBase {n : ℕ} (R S : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (y : Fin n → Values.Gamma (M := M)) : y ∈ activeBase R S ↔
      (∃ x, Fin.cons x y ∈ R ∧ Fin.cons x y ∈ S) ∧
        ∀ x, Fin.cons x y ∈ S → Fin.cons x y ∉ GammaFamilyBoundary.Boundary R := by
  change (y ∈ fibreBase (R ∩ S) ∧ y ∉ fibreBase (GammaFamilyBoundary.Boundary R ∩ S)) ↔ _
  rw [mem_fibreBase, mem_fibreBase]
  constructor
  · rintro ⟨hex, hno⟩
    exact ⟨hex, fun x hx hb => hno ⟨x, hb, hx⟩⟩
  · rintro ⟨hex, hno⟩
    exact ⟨hex, fun ⟨x, hb, hx⟩ => hno x hx hb⟩

theorem activeBase_definable (B : Base (M := M)) {n : ℕ}
    (R S : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (hS : GammaDefinable B S) : GammaDefinable B (activeBase R S) :=
  GammaRelationLogic.inter_definable_base B _ _
    (fibreBase_definable B _ (GammaRelationLogic.inter_definable_base B _ _ hR hS))
    (GammaRelationLogic.complement_definable_base B _ (fibreBase_definable B _
      (GammaRelationLogic.inter_definable_base B _ _ (GammaFamilyBoundary.boundary_definable_base B R hR) hS)))

def bandBase {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (C : Set (Fin n → Values.Gamma (M := M)))
    (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) :
    Set (Fin n → Values.Gamma (M := M)) := C ∩ {y | l y < u y} ∩ activeBase R (bandCell C l u)

def upperBase {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (C : Set (Fin n → Values.Gamma (M := M)))
    (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) :
    Set (Fin n → Values.Gamma (M := M)) := C ∩ activeBase R (upperRayCell C l)

def lowerBase {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (C : Set (Fin n → Values.Gamma (M := M)))
    (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) :
    Set (Fin n → Values.Gamma (M := M)) := C ∩ activeBase R (lowerRayCell C u)

def lineBase {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (C : Set (Fin n → Values.Gamma (M := M))) : Set (Fin n → Values.Gamma (M := M)) :=
  C ∩ activeBase R (lineCell C)

end DiamondIntegral.Section4.GammaBoundaryStackBases
