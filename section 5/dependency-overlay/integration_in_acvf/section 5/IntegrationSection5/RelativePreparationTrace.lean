import IntegrationSection5.VerticalMeanTrace

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m k : ℕ}
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
theorem relative_prepare_realRV_trace {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (h00 : M ⊨ Axioms.ACVF00)
    (A : DefSet (M := M) S (n+1) m) (hA : IsRVPullback (carrier A))
    (hTag : ∃ j, Tagged (carrier A) 0 j)
    (f : Map A (PresentedSet.univ (pointSpace (M := M) 0 k) S)) :
    ∃ T : HeadPreparation A,
      SpecialRelativeBoundary T.map 0 (some false) (some false) ∧
        (∃ j, Tagged (carrier T.target) 0 j) ∧
          (∀ b c : T.target, SameRV b.val c.val → TailEq b.val c.val →
            f (T.inverseMap b) = f (T.inverseMap c)) ∧
          ∃ W : UniformRelativeTrace S (n+1) A T.target, ∀ a : A, W.toMap a = T.map a := by
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  obtain ⟨R,d,hd,hO⟩ := uniformVerticalObstacles hs hsmall v hv (n := n) (rvGraph f) A hA
  obtain ⟨l,B,g,hg,hB,hTagB,hz,W,hW⟩ := verticalRoots_centralize_trace h00 d A R
    (headSaturated_of_pullback hA) hTag hd
  let T : HeadPreparation A := ⟨l,B,g,specialRelativeBoundary_forget hg,hB⟩
  have hRel := relative_zero_obstacles v hv (carrier (rvGraph f)) R hO T hz
  refine ⟨T,hg,hTagB,?_,W,hW⟩
  intro b c he ht
  let a := T.inverseMap b
  let a' := T.inverseMap c
  have hLabels : a.val.2 = a'.val.2 := T.inverse_labels b c ((sameRV_iff _ _).mp he).2
  let ys := Fin.append a.val.2 (f a).val.2
  have hbG : (a.val.1,ys) ∈ carrier (rvGraph f) := (mem_rvGraph f a.val (f a).val.2).mpr ⟨a,rfl,rfl⟩
  have hcG := (hRel b c he ht ys).mp hbG
  change (a'.val.1,Fin.append a.val.2 (f a).val.2) ∈ carrier (rvGraph f) at hcG
  rw [hLabels] at hcG
  obtain ⟨a'',ha'',hf⟩ := (mem_rvGraph f a'.val (f a).val.2).mp hcG
  have haa : a'' = a' := Subtype.ext ha''
  apply Subtype.ext
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · exact hf.symm.trans (congrArg (fun x : A => (f x).val.2) haa)

end IntegrationInACVF.Section5
