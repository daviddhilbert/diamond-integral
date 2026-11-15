import «section 5».KummerDescentDefinability

/-! The proved existential construction agrees with the actual original
RV carrier, not only with its normalized coordinate presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
local instance actualDescentStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem descendedOriginalSet_normalized_mem {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (X : Set (Fin n → ℂ)) (hX : (Set.univ : Set ℂ).Definable Language.ring X)
    (r : Fin n → RV) :
    (fun i => rvTag (r i)) ∈ (descendedOriginalSet N a X hX).carrier ↔
      r ∈ descendSet N a X := by
  change (fun i => rvTag (r i)) ∈ Set.range
    (fun u : descentSource N X hX => (descentMonomialMap N a X hX u).val) ↔ _
  rw [descentMonomialMap_range]
  constructor
  · rintro ⟨root, x, hx, he⟩
    exact ⟨root, x, hx, funext (fun i => congrArg taggedRVEquiv (congrFun he i))⟩
  · rintro ⟨root, x, hx, he⟩
    exact ⟨root, x, hx, congrArg (fun t => fun i => rvTag (t i)) he⟩

def actualDescendEquiv {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (X : Set (Fin n → ℂ)) (hX : (Set.univ : Set ℂ).Definable Language.ring X) :
    descendSet N a X ≃ descendedOriginalSet N a X hX where
  toFun r := ⟨fun i => rvTag (r.val i),
    (descendedOriginalSet_normalized_mem N a X hX r.val).mpr r.property⟩
  invFun u := ⟨fun i => taggedRVEquiv (u.val i), by
    apply (descendedOriginalSet_normalized_mem N a X hX _).mp
    have he : (fun i => rvTag (taggedRVEquiv (u.val i))) = u.val :=
      funext (fun i => taggedRVEquiv.symm_apply_apply (u.val i))
    exact Eq.mpr (congrArg (fun t => t ∈ (descendedOriginalSet N a X hX).carrier) he) u.property⟩
  left_inv r := Subtype.ext rfl
  right_inv u := Subtype.ext (funext (fun i => taggedRVEquiv.symm_apply_apply (u.val i)))

def actualDescendedBijection {n m : ℕ} (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (X : Set (Fin n → ℂ)) (Y : Set (Fin m → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X)
    (hY : (Set.univ : Set ℂ).Definable Language.ring Y)
    (hiX : FiniteInvariant N a X) (hiY : FiniteInvariant N b Y) (e : X ≃ Y) :
    descendedOriginalSet N a X hX ≃ descendedOriginalSet N b Y hY :=
  ((actualDescendEquiv N a X hX).symm.trans (descendedBijection N a b X Y hiX hiY e)).trans
    (actualDescendEquiv N b Y hY)

end DiamondIntegral.Section5.PuiseuxOriginal
