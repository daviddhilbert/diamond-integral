import «section 6».TailContinuousFullFocusGraphs
import «section 6».UncurriedFamilyMapValues
import «section 6».FocusComponentTemplateRealizations

/-! A component formula chosen on the coordinate fibres assembles to
a joint focus graph with continuous tail fibres. Its first VF coordinate
is the parameter; its target remains the specified other coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def FocusComponentParameterTemplate.jointFocusGraph
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : FocusComponentParameterTemplate (M := M) S 1 n r)
    (A : MixedSetParameterTemplate (M := M) S 1 n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n r)
    (hGood : ∀ x ∈ A.uncurry.carrier,(fun _ : Fin 1 => (x.1 0).val) ∈ T.good A P)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (hLocus : ∀ x ∈ A.uncurry.carrier,x.2 ∈ U.carrier ↔
      x.2 ∈ (T.active.fibre (fun _ => (x.1 0).val)).carrier)
    (hA : ProperInvariant S A.uncurry.carrier) (hAD : VFDoublyBounded A.uncurry.carrier)
    (hTag : ∀ x ∈ A.uncurry.carrier,∀ y ∈ A.uncurry.carrier,x.2=y.2 → tupleRV M x.1=tupleRV M y.1) :
    TailContinuousFullFocusGraphData (G := G) A.uncurry := by
  let C := focusActive A.uncurry U
  have hFGood : ∀ x ∈ C.carrier,(fun _ : Fin 1 => (x.1 0).val) ∈ T.focus.good :=
    fun x hx => (hGood x hx.1).1.1.1
  let f := uncurriedFamilyMap T.focus C hFGood
  refine {
    coordinate := T.coordinate.succ
    notHead := Fin.succ_ne_zero _
    activeTags := U
    map := f
    independent := ?_
    proper := hA
    doublyBounded := hAD
    tagged := hTag
    continuousTail := uncurriedFamilyMap_tail_continuous hv T.focus C hFGood
    leadingTerm := ?_ }
  · intro p q hTags hOther
    have hHead : p.val.1 0=q.val.1 0 := hOther 0 (Fin.succ_ne_zero T.coordinate).symm
    let a : Fin 1 → M := fun _ => (p.val.1 0).val
    have hParam : (fun _ : Fin 1 => (q.val.1 0).val)=a :=
      funext (fun _ => congrArg Subtype.val hHead.symm)
    have ha : a ∈ T.good A P := hGood p.val p.property.1
    let g := rvFamilyMap (focusActive (A.fibre a) (T.active.fibre a)) (T.focus.value a ha.1.1.1)
      (T.focus.family_graph_definable a ha.1.1.1)
    have hGraph := focusGraphParameterCode_at A T.active T.focus a ha.1.1.1
    have hIndependent := (mem_focusIndependentParameterLocus_map_iff
      (focusGraphParameterCode A T.active T.focus) a T.coordinate g hGraph).mp ha.2.1.1.2
    have hpA : (Fin.tail p.val.1,p.val.2) ∈ (A.fibre a).carrier :=
      (A.mem_uncurry_iff p.val).mp p.property.1
    have hqA : (Fin.tail q.val.1,q.val.2) ∈ (A.fibre a).carrier := by
      have h := (A.mem_uncurry_iff q.val).mp q.property.1
      rw [hParam] at h
      exact h
    have hpU : p.val.2 ∈ (T.active.fibre a).carrier := (hLocus p.val p.property.1).mp p.property.2
    have hqU : q.val.2 ∈ (T.active.fibre a).carrier := by
      have h := (hLocus q.val q.property.1).mp q.property.2
      rw [hParam] at h
      exact h
    have hLocal := hIndependent ⟨(Fin.tail p.val.1,p.val.2),hpA,hpU⟩
      ⟨(Fin.tail q.val.1,q.val.2),hqA,hqU⟩ hTags
        (fun i hi => hOther i.succ (fun he => hi (Fin.succ_injective _ he)))
    change (uncurriedFamilyMap T.focus C hFGood p).val 0=(uncurriedFamilyMap T.focus C hFGood q).val 0
    rw [uncurriedFamilyMap_value,uncurriedFamilyMap_value]
    simpa only [g,rvFamilyMap,a,hHead] using hLocal
  · intro p
    let a : Fin 1 → M := fun _ => (p.val.1 0).val
    have ha : a ∈ T.good A P := hGood p.val p.property.1
    let g := rvFamilyMap (focusActive (A.fibre a) (T.active.fibre a)) (T.focus.value a ha.1.1.1)
      (T.focus.family_graph_definable a ha.1.1.1)
    have hGraph := focusGraphParameterCode_at A T.active T.focus a ha.1.1.1
    have hLeading := (mem_focusLeadingTermParameterLocus_map_iff
      (focusGraphParameterCode A T.active T.focus) a T.coordinate g hGraph).mp ha.2.1.2
    have hpA : (Fin.tail p.val.1,p.val.2) ∈ (A.fibre a).carrier :=
      (A.mem_uncurry_iff p.val).mp p.property.1
    have hpU : p.val.2 ∈ (T.active.fibre a).carrier := (hLocus p.val p.property.1).mp p.property.2
    have h := hLeading ⟨(Fin.tail p.val.1,p.val.2),hpA,hpU⟩
    change rv M ((uncurriedFamilyMap T.focus C hFGood p).val 0)=rv M (p.val.1 T.coordinate.succ)
    rw [uncurriedFamilyMap_value]
    exact h

end DiamondIntegral.Section6
