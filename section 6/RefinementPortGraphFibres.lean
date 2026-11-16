import «section 6».RetainedRVOutputMaps

/-! Apply an actual base map through an RV refinement, retaining every
refining label. The full graph lies over the original map graph, and
its source is the exact intersection of the two actual source fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

def RVRefinementFrame.portMap (hc : CanonicalStructure.IsCanonical (M := M))
    (X : RVRefinementFrame A) (f : Map A B) := retainedRVOutput hc (f.comp X.oldMap)

theorem RVRefinementFrame.portMap_value (hc : CanonicalStructure.IsCanonical (M := M))
    (X : RVRefinementFrame A) (f : Map A B) (p : X.base) :
    (X.portMap hc f p).val=((f (X.oldPoint p)).val.1,Fin.append (f (X.oldPoint p)).val.2 p.val.2) := rfl

theorem RVRefinementFrame.port_graph_lies_over (hc : CanonicalStructure.IsCanonical (M := M))
    (X : RVRefinementFrame A) (f : Map A B)
    (u : Fin X.arity → RVInfinity M) (v : Fin (s+X.arity) → RVInfinity M)
    (a : Fin n → VF M) (b : Fin m → VF M)
    (h : graphFibre (X.portMap hc f) u v a b) :
    graphFibre f (u ∘ X.labels) (v ∘ Fin.castAdd X.arity) a b := by
  obtain ⟨p,hp,hfp⟩ := h
  refine ⟨X.oldPoint p,?_,?_⟩
  · exact congrArg (fun q : Mixed M n X.arity => (q.1,q.2 ∘ X.labels)) hp
  · have hSelect := retainedRVOutput_selected hc (f.comp X.oldMap) p
    change ((X.portMap hc f p).val.1,(X.portMap hc f p).val.2 ∘ Fin.castAdd X.arity)=(f (X.oldPoint p)).val at hSelect
    rw [hfp] at hSelect
    exact hSelect.symm

theorem RVRefinementFrame.port_source_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (X : RVRefinementFrame A) (f : Map A B)
    (u : Fin X.arity → RVInfinity M) (v : Fin (s+X.arity) → RVInfinity M) (a : Fin n → VF M) :
    a ∈ graphFibreSource (X.portMap hc f) u v ↔
      u=v ∘ Fin.natAdd s ∧ (a,u) ∈ X.base.carrier ∧
      a ∈ graphFibreSource f (u ∘ X.labels) (v ∘ Fin.castAdd X.arity) := by
  constructor
  · rintro ⟨b,p,hp,hfp⟩
    have hTail : u=v ∘ Fin.natAdd s := by
      funext i
      have h := congrArg (fun q : Mixed M m (s+X.arity) => q.2 (Fin.natAdd s i)) hfp
      simpa only [RVRefinementFrame.portMap_value,Fin.append_right,Function.comp_apply,congrArg (fun q : Mixed M n X.arity => q.2 i) hp] using h
    exact ⟨hTail,hp ▸ p.property,b,X.port_graph_lies_over hc f u v a b ⟨p,hp,hfp⟩⟩
  · rintro ⟨hTail,hx,y,b,hb,hfb⟩
    let p : X.base := ⟨(a,u),hx⟩
    have hOld : b=X.oldPoint p := Subtype.ext hb
    have hTags : (f (X.oldPoint p)).val.2=v ∘ Fin.castAdd X.arity := by
      rw [← hOld]
      exact congrArg Prod.snd hfb
    refine ⟨(f (X.oldPoint p)).val.1,p,rfl,?_⟩
    apply Prod.ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [RVRefinementFrame.portMap_value,Fin.append_left,Function.comp_apply] using congrFun hTags j
      · simpa only [RVRefinementFrame.portMap_value,Fin.append_right,Function.comp_apply] using congrFun hTail j

theorem RVRefinementFrame.port_graph_source (hc : CanonicalStructure.IsCanonical (M := M))
    (X : RVRefinementFrame A) (f : Map A B)
    (u : Fin X.arity → RVInfinity M) (v : Fin (s+X.arity) → RVInfinity M) :
    graphFibreSource (X.portMap hc f) u v=if u=v ∘ Fin.natAdd s then
      vfFibre X.base.carrier u ∩ graphFibreSource f (u ∘ X.labels) (v ∘ Fin.castAdd X.arity) else ∅ := by
  ext a
  rw [X.port_source_iff hc f u v a]
  split_ifs with h
  · exact and_iff_right h
  · simp only [h,false_and,Set.mem_empty_iff_false]

theorem RVRefinementFrame.port_graphMap_agrees (hc : CanonicalStructure.IsCanonical (M := M))
    (X : RVRefinementFrame A) (f : Map A B)
    (u : Fin X.arity → RVInfinity M) (v : Fin (s+X.arity) → RVInfinity M) :
    Set.EqOn (graphFibreMap (X.portMap hc f) u v)
      (graphFibreMap f (u ∘ X.labels) (v ∘ Fin.castAdd X.arity)) (graphFibreSource (X.portMap hc f) u v) := by
  intro a ha
  have hSource := ((X.port_source_iff hc f u v a).mp ha).2.2
  exact graphFibre_functional f _ _
    (X.port_graph_lies_over hc f u v a _ (graphFibreMap_graph _ _ _ ha)) (graphFibreMap_graph _ _ _ hSource)

end DiamondIntegral.Section6
