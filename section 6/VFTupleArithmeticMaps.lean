import «section 6».ScalarCodeAlgebra
import «section 6».MixedTupleDifferentiability

/-! Actual same-base tuple addition, subtraction and constant one maps.
These maps are used to recover the affine tail coefficients from its
already checked definable evaluation graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {m : ℕ}

inductive VFTupleBinaryOp where
  | add | sub

def VFTupleBinaryOp.value (op : VFTupleBinaryOp) (x y : VF M) : VF M :=
  match op with | .add => x+y | .sub => x-y

def VFTupleBinaryOp.code (op : VFTupleBinaryOp) (x y : M) : M :=
  match op with | .add => iVFAdd x y | .sub => iVFAdd x (iVFNeg y)

theorem VFTupleBinaryOp.code_definable (op : VFTupleBinaryOp) {I : Type}
    {f g : (I → M) → M} (hf : S.DefinableFun LRV f) (hg : S.DefinableFun LRV g) :
    S.DefinableFun LRV (fun z => op.code (f z) (g z)) := by
  cases op
  · exact scalarAddCode_definable hf hg
  · exact scalarSubCode_definable hf hg

theorem VFTupleBinaryOp.value_code (op : VFTupleBinaryOp) (x y : VF M) :
    (op.value x y).val = op.code x.val y.val := by
  cases op <;> rfl

def vfTupleBinaryMap (S : Set M) (op : VFTupleBinaryOp) :
    Map (DefSet.univ ((rawVFSpace (M := M) m).prod (rawVFSpace m)) S)
      (DefSet.univ (rawVFSpace (M := M) m) S) := by
  let P := (rawVFSpace (M := M) m).prod (rawVFSpace m)
  let Q := rawVFSpace (M := M) m
  let f (p : P.Carrier) : Q.Carrier := fun i => op.value (p.1 i) (p.2 i)
  let F (z : P.Index → M) : Q.Index → M := fun i => op.code (z (.inl i)) (z (.inr i))
  have hF : S.DefinableMap LRV F := fun _ => op.code_definable
    (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV)
  have hcode (c : P.domain) : vfValues (f (P.decode c)) = F c.val := by
    have h₁ := vfValues_decode (⟨fun i => c.val (.inl i),c.property.1⟩ : (rawVFSpace (M := M) m).domain)
    have h₂ := vfValues_decode (⟨fun i => c.val (.inr i),c.property.2⟩ : (rawVFSpace (M := M) m).domain)
    funext i
    change (op.value ((P.decode c).1 i) ((P.decode c).2 i)).val = _
    rw [op.value_code]
    exact congrArg₂ op.code (congrFun h₁ i) (congrFun h₂ i)
  refine Map.ofCodes (DefSet.univ P S) f F hF
    (fun c => ⟨f (P.decode c),hcode c⟩) ?_
  intro c
  exact vfValues_injective ((vfValues_decode _).trans (hcode c).symm)

theorem vfTupleBinaryMap_value (S : Set M) (op : VFTupleBinaryOp)
    (p : DefSet.univ ((rawVFSpace (M := M) m).prod (rawVFSpace m)) S) :
    (vfTupleBinaryMap S op p).val = fun i => op.value (p.val.1 i) (p.val.2 i) := rfl

def vfTupleOnesMap {P : SpecialTransformations.DefinableGeometry.Space LRV M} (A : DefSet P S) :
    Map A (DefSet.univ (rawVFSpace (M := M) m) S) := by
  let Q := rawVFSpace (M := M) m
  let F (_ : P.Index → M) : Fin m → M := fun _ => iVFOne
  have hF : S.DefinableMap LRV F := fun _ =>
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfOne)).comp
      (fun i => i.elim0)
  have hDom (c : P.domain) : F c.val ∈ Q.domain := ⟨fun _ => 1,rfl⟩
  refine Map.ofCodes A (fun _ => fun _ => 1) F hF hDom ?_
  intro c
  apply vfValues_injective
  exact vfValues_decode _

theorem vfTupleOnesMap_value {P : SpecialTransformations.DefinableGeometry.Space LRV M}
    (A : DefSet P S) (p : A) : (vfTupleOnesMap (m := m) A p).val = fun _ => 1 := rfl

end DiamondIntegral.Section6
