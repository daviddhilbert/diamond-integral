import «section 5».ActualKummerDescent
import «section 5».NormalizedGraphDescent

/-! The inverse graph identity on the actual original RV carrier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
local instance actualGraphStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem actual_descended_graph {n m : ℕ} (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (X : Set (Fin n → ℂ)) (Y : Set (Fin m → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X)
    (hY : (Set.univ : Set ℂ).Definable Language.ring Y)
    (hiX : FiniteInvariant N a X) (hiY : FiniteInvariant N b Y) (e : X ≃ Y)
    (hG : (Set.univ : Set ℂ).Definable Language.ring (framedEquivGraph X Y e))
    (hiG : FiniteInvariant N (Fin.append a b) (framedEquivGraph X Y e))
    (u : descendedOriginalSet N a X hX) (v : descendedOriginalSet N b Y hY) :
    Fin.append u.val v.val ∈
        (descendedOriginalSet N (Fin.append a b) (framedEquivGraph X Y e) hG).carrier ↔
      actualDescendedBijection N a b X Y hX hY hiX hiY e u = v := by
  let E := actualDescendEquiv N a X hX
  let F := actualDescendEquiv N b Y hY
  let nu := E.symm u
  let nv := F.symm v
  have hu : (fun i => rvTag (nu.val i)) = u.val := congrArg Subtype.val (E.apply_symm_apply u)
  have hv : (fun j => rvTag (nv.val j)) = v.val := congrArg Subtype.val (F.apply_symm_apply v)
  have ht : (fun i => rvTag (Fin.append nu.val nv.val i)) = Fin.append u.val v.val := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using congrFun hu j
    · simpa only [Fin.append_right] using congrFun hv j
  have hm := descendedOriginalSet_normalized_mem N (Fin.append a b)
    (framedEquivGraph X Y e) hG (Fin.append nu.val nv.val)
  rw [ht] at hm
  rw [hm, normalized_descended_graph N a b X Y hiX hiY e hiG nu nv]
  constructor
  · intro h
    change F (descendedBijection N a b X Y hiX hiY e nu) = v
    rw [h]
    exact F.apply_symm_apply v
  · intro h
    have hh := congrArg F.symm h
    change F.symm (F (descendedBijection N a b X Y hiX hiY e nu)) = nv at hh
    rwa [F.symm_apply_apply] at hh

end DiamondIntegral.Section5.PuiseuxOriginal
