import «section 6».RVResidualDimensionDrop

/-! Actual original-base RV scalar arithmetic maps, using the existing
multiplication, inverse and one symbols of LRV. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ} {I : Type}

theorem scalarRVMulCode_definable {f g : (I → M) → M}
    (hf : S.DefinableFun LRV f) (hg : S.DefinableFun LRV g) :
    S.DefinableFun LRV (fun z => iRVMul (f z) (g z)) := by
  have h : S.DefinableMap LRV (fun z => ![f z,g z]) := by
    intro i
    fin_cases i
    · exact hf
    · exact hg
  exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp h

theorem scalarRVInvCode_definable {f : (I → M) → M} (hf : S.DefinableFun LRV f) :
    S.DefinableFun LRV (fun z => iRVInvFn (f z)) := by
  have h : S.DefinableMap LRV (fun z => ![f z]) := by intro i; fin_cases i; exact hf
  exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvInv)).comp h

def rvScalarMapOfCodes (S : Set M) (f : (Fin n → RVInfinity M) → RVInfinity M)
    (F : (Fin n → M) → M) (hF : S.DefinableFun LRV F)
    (hCode : ∀ c : (rawRVSpace (M := M) n).domain, F c.val = (f ((rawRVSpace n).decode c)).val) :
    Map (DefSet.univ (rawRVSpace (M := M) n) S) (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let P := rawRVSpace (M := M) n
  let Q := rawRVSpace (M := M) 1
  let C (z : Fin n → M) : Fin 1 → M := fun _ => F z
  have hdom (c : P.domain) : C c.val ∈ Q.domain := by
    refine ⟨fun _ => f (P.decode c),funext (fun _ => ?_)⟩
    exact (hCode c).symm
  refine Map.ofCodes (DefSet.univ P S) (fun t => fun _ : Fin 1 => f t) C (fun _ => hF) hdom ?_
  intro c
  apply rvValues_injective
  have h : rvValues (Q.decode ⟨C c.val,hdom c⟩) = C c.val := rvValues_decode _
  refine h.trans (funext (fun _ => hCode c))

def rvScalarMulMap (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) 2) S) (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  refine rvScalarMapOfCodes S (fun t : Fin 2 → RVInfinity M => t 0*t 1)
    (fun z : Fin 2 → M => iRVMul (z 0) (z 1))
    (scalarRVMulCode_definable (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV)) ?_
  intro c
  have h0 := congrFun (rvValues_decode c) (0 : Fin 2)
  have h1 := congrFun (rvValues_decode c) (1 : Fin 2)
  change (((rawRVSpace (M := M) 2).decode c) 0).val = c.val (0 : Fin 2) at h0
  change (((rawRVSpace (M := M) 2).decode c) 1).val = c.val (1 : Fin 2) at h1
  rw [RVOperations.mul_val,h0,h1]

def rvScalarDivMap (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) 2) S) (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  refine rvScalarMapOfCodes S (fun t : Fin 2 → RVInfinity M => t 0/t 1)
    (fun z : Fin 2 → M => iRVMul (z 0) (iRVInvFn (z 1)))
    (scalarRVMulCode_definable (Set.DefinableFun.proj LRV) (scalarRVInvCode_definable (Set.DefinableFun.proj LRV))) ?_
  intro c
  have h0 := congrFun (rvValues_decode c) (0 : Fin 2)
  have h1 := congrFun (rvValues_decode c) (1 : Fin 2)
  change (((rawRVSpace (M := M) 2).decode c) 0).val = c.val (0 : Fin 2) at h0
  change (((rawRVSpace (M := M) 2).decode c) 1).val = c.val (1 : Fin 2) at h1
  rw [div_eq_mul_inv,RVOperations.mul_val,RVOperations.inv_val,h0,h1]

theorem rvScalarMulMap_value (S : Set M) (t : DefSet.univ (rawRVSpace (M := M) 2) S) :
    (rvScalarMulMap S t).val 0 = t.val 0*t.val 1 := rfl

theorem rvScalarDivMap_value (S : Set M) (t : DefSet.univ (rawRVSpace (M := M) 2) S) :
    (rvScalarDivMap S t).val 0 = t.val 0/t.val 1 := rfl

end DiamondIntegral.Section6
