import IntegrationSection5.ScalarRealPresentation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

def scalarCentreMap (A : DefSet (M := M) S n m) (c : Point (M := M) n m → VF (M := M))
    (hc : RelationDefinable (pointSpace n m) (SpecialTransformations.Section4.vfSpace 1) S
      (fun p z => p ∈ carrier A ∧ z 0 = c p)) :
    Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) :=
  Map.mk (fun a => ⟨![c a.val],Set.mem_univ _⟩)
    (RelationDefinable.congr _ _ hc (by
      intro p z
      constructor
      · rintro ⟨hp,hz⟩
        refine ⟨⟨p,hp⟩,rfl,?_⟩
        funext j
        fin_cases j
        exact hz.symm
      · rintro ⟨a,ha,hz⟩
        exact ⟨ha ▸ a.property,(congrFun hz 0).symm.trans (congrArg c ha)⟩))

theorem scalarCentreMap_apply (A : DefSet (M := M) S n m) (c : Point (M := M) n m → VF (M := M))
    (hc : RelationDefinable (pointSpace n m) (SpecialTransformations.Section4.vfSpace 1) S
      (fun p z => p ∈ carrier A ∧ z 0 = c p)) (a : A) : (scalarCentreMap A c hc a).val 0 = c a.val := rfl

end IntegrationInACVF.Section5
