import «section 6».OriginalBaseRVBoundaries

/-! Actual original-base VF projection maps, either to the pure VF
presentation or to the mixed presentation with no RV coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def mixedVFHeadMap (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Map A (DefSet.univ (rawVFSpace (M := M) n) S) := by
  let P := rawMixedSpace (M := M) n r
  let F (z : P.Index → M) := z ∘ Sum.inl
  have hCode (c : P.domain) : vfValues (P.decode c).1 = F c.val := by
    funext i
    exact congrFun (mixedValues_decode c) (.inl i)
  refine Map.ofCodes A Prod.fst F (fun _ => Set.DefinableFun.proj LRV)
    (fun c => ⟨(P.decode c).1,hCode c⟩) ?_
  intro c
  exact vfValues_injective ((vfValues_decode _).trans (hCode c).symm)

theorem mixedVFHeadMap_value (A : DefSet (rawMixedSpace (M := M) n r) S) (u : A) :
    (mixedVFHeadMap A u).val = u.val.1 := rfl

def mixedEraseRVMap (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n 0) S) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) n 0
  let F (z : P.Index → M) : Q.Index → M := Sum.elim (z ∘ Sum.inl) Fin.elim0
  have hCode (c : P.domain) : mixedValues ((P.decode c).1,Fin.elim0) = F c.val := by
    funext i
    rcases i with i | i
    · exact congrFun (mixedValues_decode c) (.inl i)
    · exact i.elim0
  have hDom (c : P.domain) : F c.val ∈ Q.domain := by
    rw [← hCode c]
    exact mixedValues_mem_domain _
  refine Map.ofCodes A (fun x => (x.1,Fin.elim0)) F
    (fun i => by cases i with | inl i => exact Set.DefinableFun.proj LRV | inr i => exact i.elim0) hDom ?_
  intro c
  exact mixedValues_injective ((mixedValues_decode _).trans (hCode c).symm)

theorem mixedEraseRVMap_value (A : DefSet (rawMixedSpace (M := M) n r) S) (u : A) :
    (mixedEraseRVMap A u).val = (u.val.1,Fin.elim0) := rfl

end DiamondIntegral.Section6
