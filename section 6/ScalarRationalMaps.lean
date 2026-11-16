import «section 6».PureRVScalarCenters
import «section 2».DefinableVFInverse
import «section 6».ScalarCodeAlgebra

/-! A definable rational scalar map on three VF inputs. The inverse
operation is defined by its field graph, rather than added to LRV. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def scalarRatioMulMap (S : Set M) :
    Map (DefSet.univ (((rawVFSpace (M := M) 1).prod (rawVFSpace 1)).prod (rawVFSpace 1)) S)
      (DefSet.univ (rawVFSpace (M := M) 1) S) := by
  let P := ((rawVFSpace (M := M) 1).prod (rawVFSpace 1)).prod (rawVFSpace 1)
  let Q := rawVFSpace (M := M) 1
  let F (z : (Fin 1 ⊕ Fin 1) ⊕ Fin 1 → M) : Fin 1 → M := fun _ =>
    iVFMul (iVFMul (z (.inl (.inl 0))) (rawVFInverse (z (.inl (.inr 0))))) (z (.inr 0))
  have hF : S.DefinableMap LRV F := fun _ => scalarMulCode_definable
    (scalarMulCode_definable (Set.DefinableFun.proj LRV) (rawVFInverse_definable S _))
    (Set.DefinableFun.proj LRV)
  let f (p : P.Carrier) : Fin 1 → VF M := fun _ => p.1.1 0 / p.1.2 0 * p.2 0
  have hcode (c : P.domain) (i : Fin 1) : F c.val i = (f (P.decode c) i).val := by
    have ha := congrFun (vfValues_decode
      (⟨fun i : Fin 1 => c.val (.inl (.inl i)),c.property.1.1⟩ : (rawVFSpace (M := M) 1).domain)) (0 : Fin 1)
    have hb := congrFun (vfValues_decode
      (⟨fun i : Fin 1 => c.val (.inl (.inr i)),c.property.1.2⟩ : (rawVFSpace (M := M) 1).domain)) (0 : Fin 1)
    have hx := congrFun (vfValues_decode
      (⟨fun i : Fin 1 => c.val (.inr i),c.property.2⟩ : (rawVFSpace (M := M) 1).domain)) (0 : Fin 1)
    change ((P.decode c).1.1 (0 : Fin 1)).val = c.val (.inl (.inl (0 : Fin 1))) at ha
    change ((P.decode c).1.2 (0 : Fin 1)).val = c.val (.inl (.inr (0 : Fin 1))) at hb
    change ((P.decode c).2 (0 : Fin 1)).val = c.val (.inr (0 : Fin 1)) at hx
    change iVFMul (iVFMul _ (rawVFInverse _)) _ = _
    rw [← ha,← hb,← hx,rawVFInverse_vf]
    rfl
  have hdom (c : P.domain) : F c.val ∈ Q.domain := by
    refine ⟨f (P.decode c),?_⟩
    funext i
    exact (hcode c i).symm
  refine Map.ofCodes (DefSet.univ P S) f F hF hdom ?_
  intro c
  apply vfValues_injective
  exact (vfValues_decode ⟨F c.val,hdom c⟩).trans (funext (hcode c))

theorem scalarRatioMulMap_value (S : Set M)
    (p : DefSet.univ (((rawVFSpace (M := M) 1).prod (rawVFSpace 1)).prod (rawVFSpace 1)) S) :
    (scalarRatioMulMap S p).val 0 = p.val.1.1 0 / p.val.1.2 0 * p.val.2 0 := rfl

end DiamondIntegral.Section6
