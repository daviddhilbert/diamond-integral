import «section 6».RVLabelTranslations

/-! Actual definable coordinate masks and interpolations between the
source and target VF coordinates of a full definable map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

def vfMaskMap (S : Set M) (P : Fin n → Prop) :
    Map (DefSet.univ (rawVFSpace (M := M) n) S) (DefSet.univ (rawVFSpace (M := M) n) S) := by
  let V := rawVFSpace (M := M) n
  let f (x : Fin n → VF M) : Fin n → VF M := fun i => if P i then x i else 0
  let F (z : Fin n → M) : Fin n → M := fun i => if P i then z i else iVFZero
  have hZero : S.DefinableFun LRV (fun _ : Fin n → M => iVFZero) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfZero)).comp (fun i => i.elim0)
  have hF : S.DefinableMap LRV F := by
    intro i
    by_cases hi : P i
    · simpa only [F,if_pos hi] using (Set.DefinableFun.proj LRV (i := i) : S.DefinableFun LRV (fun z : Fin n → M => z i))
    · simpa only [F,if_neg hi] using hZero
  have hCode (c : V.domain) : vfValues (f (V.decode c))=F c.val := by
    funext i
    change (f (V.decode c) i).val=F c.val i
    by_cases hi : P i
    · simp only [f,F,if_pos hi]
      exact congrFun (vfValues_decode c) i
    · simp only [f,F,if_neg hi]
      rfl
  have hDom (c : V.domain) : F c.val ∈ V.domain := ⟨f (V.decode c),hCode c⟩
  refine Map.ofCodes (DefSet.univ V S) f F hF hDom ?_
  intro c
  exact vfValues_injective ((vfValues_decode ⟨_,hDom c⟩).trans (hCode c).symm)

theorem vfMaskMap_value (S : Set M) (P : Fin n → Prop)
    (p : DefSet.univ (rawVFSpace (M := M) n) S) :
    (vfMaskMap S P p).val=fun i => if P i then p.val i else 0 := rfl

variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

def vfInterpolationMap (f : Map A B) (P : Fin n → Prop) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n s) S) := by
  let F := (vfMaskMap S P).comp ((mixedVFHeadMap B).comp f)
  let H := (vfMaskMap S (fun i => ¬ P i)).comp (mixedVFHeadMap A)
  let V := (vfTupleBinaryMap S .add).comp ((Map.inclusion (fun _ _ => Set.mem_univ _)).comp (F.pair H))
  exact (Map.inclusion (fun _ _ => Set.mem_univ _)).comp (V.pair ((rvTailMap B).comp f))

def vfInterpolation (f : Map A B) (P : Fin n → Prop) := (vfInterpolationMap f P).toImage

theorem vfInterpolation_value (f : Map A B) (P : Fin n → Prop) (p : A) :
    (vfInterpolation f P p).val=((fun i => if P i then (f p).val.1 i else p.val.1 i),(f p).val.2) := by
  apply Prod.ext
  · funext i
    dsimp only [vfInterpolation,vfInterpolationMap,Map.comp,Map.toImage,Map.pair,Map.inclusion]
    rw [vfTupleBinaryMap_value,vfMaskMap_value,vfMaskMap_value]
    dsimp only [VFTupleBinaryOp.value]
    rw [mixedVFHeadMap_value,mixedVFHeadMap_value]
    by_cases hi : P i <;> simp only [hi,not_true_eq_false,not_false_eq_true,if_true,if_false,add_zero,zero_add]
  · rfl

theorem vfInterpolation_coordinate (f : Map A B) (P : Fin n → Prop) (p : A) (i : Fin n) :
    (vfInterpolation f P p).val.1 i=if P i then (f p).val.1 i else p.val.1 i := by
  rw [vfInterpolation_value]

theorem vfInterpolation_tags (f : Map A B) (P : Fin n → Prop) (p : A) :
    (vfInterpolation f P p).val.2=(f p).val.2 := by
  rw [vfInterpolation_value]

end DiamondIntegral.Section6
