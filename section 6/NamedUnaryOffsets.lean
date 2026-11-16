import «section 6».UnaryOffsetCoreFibres

/-! A single original-base named VF coefficient gives an actual
label-definable offset map on every center fibre. Positive valuation
places its offset strictly inside the center's old RV disc. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def namedVFScalarMulMap (c : VF M) (hc : S.Definable₁ LRV {c.val}) :
    Map (DefSet.univ (rawVFSpace (M := M) 1) S) (DefSet.univ (rawVFSpace (M := M) 1) S) := by
  let P := rawVFSpace (M := M) 1
  let f (x : Fin 1 → VF M) : Fin 1 → VF M := fun i => c*x i
  let F (z : Fin 1 → M) : Fin 1 → M := fun i => iVFMul c.val (z i)
  have hF : S.DefinableMap LRV F := fun _ => scalarMulCode_definable
    (definable_named_constant c.val hc) (Set.DefinableFun.proj LRV)
  have hCode (z : P.domain) : vfValues (f (P.decode z))=F z.val := by
    funext i
    exact congrArg (iVFMul c.val) (congrFun (vfValues_decode z) i)
  exact Map.ofCodes (DefSet.univ P S) f F hF (fun z => ⟨f (P.decode z),hCode z⟩)
    (fun z => vfValues_injective ((vfValues_decode _).trans (hCode z).symm))

theorem namedVFScalarMulMap_value (c : VF M) (hc : S.Definable₁ LRV {c.val})
    (p : DefSet.univ (rawVFSpace (M := M) 1) S) :
    (namedVFScalarMulMap c hc p).val 0=c*p.val 0 := rfl

theorem vf_value_lt_positive_named_offset (a c : VF M) (ha : a ≠ 0) (hc : c ≠ 0)
    (hcpos : (1 : GammaInfinity M) < vfValue c) : vfValue a < vfValue (c*a) := by
  have hh : finiteValue a ha < finiteValue c hc*finiteValue a ha := by
    simpa only [one_mul] using mul_lt_mul_left (show (1 : Gamma M) < finiteValue c hc from hcpos) (finiteValue a ha)
  change vfValue a < vfValue c*vfValue a at hh
  change vfValue a < Values.vfValueHom (c*a)
  rw [map_mul,valueHom_eq_value,valueHom_eq_value]
  exact hh

namespace UnaryFocusData
variable {r : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable (F : UnaryFocusData A)

def namedOffsetMap (c : VF M) (hc : S.Definable₁ LRV {c.val}) :=
  (namedVFScalarMulMap c hc).comp F.focusMap

theorem namedOffsetMap_value (c : VF M) (hc : S.Definable₁ LRV {c.val}) (p : focusActive A F.activeTags) :
    (F.namedOffsetMap c hc p).val 0=c*F.focus p.val.2 := by
  change c*(F.focusMap p).val 0=_
  rw [F.focusMap_eq]

end UnaryFocusData
end DiamondIntegral.Section6
