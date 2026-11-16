import «section 6».UnaryIndexedContinuousMaps
import «section 6».JointComponentFocusGraphs

/-! Component formulas assemble into actual continuous-tail focus
graphs on joint ambients at an RV-dependent old parameter. Current
properness and the actual whole-label locus are explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem mem_unaryIndexedMixedFamily_at
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : MixedSetParameterTemplate (M := M) S 1 n s)
    (p : Mixed M (n+1) (r+s)) (b : B) (hb : unaryFamilyBasePoint p=b.val) :
    p ∈ (unaryIndexedMixedFamily η T).carrier ↔
      (Fin.tail p.1,p.2 ∘ Fin.natAdd r) ∈ (T.fibre (unaryFamilyParameter η b)).carrier := by
  rw [mem_unaryIndexedMixedFamily]
  constructor
  · rintro ⟨c,hc,hT⟩
    have he : c=b := Subtype.ext (hc.symm.trans hb)
    exact he ▸ hT
  · intro hT
    exact ⟨b,hb,hT⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def FocusComponentParameterTemplate.unaryIndexedFocusGraph
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : FocusComponentParameterTemplate (M := M) S 1 n s)
    (A : MixedSetParameterTemplate (M := M) S 1 n s)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s)
    (W : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hW : W.carrier ⊆ (unaryIndexedMixedFamily η A).carrier)
    (hGood : ∀ p ∈ W.carrier,∀ b : B,unaryFamilyBasePoint p=b.val →
      unaryFamilyParameter η b ∈ T.good A P)
    (U : DefSet (rawRVSpace (M := M) (r+s)) S)
    (hLocus : ∀ p ∈ W.carrier,∀ b : B,unaryFamilyBasePoint p=b.val →
      (p.2 ∈ U.carrier ↔ p.2 ∘ Fin.natAdd r ∈ (T.active.fibre (unaryFamilyParameter η b)).carrier))
    (hProper : ProperInvariant S W.carrier) (hDouble : VFDoublyBounded W.carrier)
    (hTag : ∀ p ∈ W.carrier,∀ q ∈ W.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    TailContinuousFullFocusGraphData (G := G) W := by
  let C := focusActive W U
  have hBase : ∀ p ∈ C.carrier,unaryFamilyBasePoint p ∈ B.carrier := by
    intro p hp
    obtain ⟨b,hb,hA⟩ := (mem_unaryIndexedMixedFamily η A p).mp (hW hp.1)
    exact hb.symm ▸ b.property
  have hFGood : ∀ p ∈ C.carrier,∀ b : B,unaryFamilyBasePoint p=b.val →
      unaryFamilyParameter η b ∈ T.focus.good :=
    fun p hp b hb => (hGood p hp.1 b hb).1.1.1
  let f := unaryIndexedFamilyMap η T.focus C hBase hFGood
  refine {
    coordinate := T.coordinate.succ
    notHead := Fin.succ_ne_zero _
    activeTags := U
    map := f
    independent := ?_
    proper := hProper
    doublyBounded := hDouble
    tagged := hTag
    continuousTail := unaryIndexedFamilyMap_tail_continuous hv η T.focus C hBase hFGood
    leadingTerm := ?_ }
  · intro p q hTags hOther
    let b : B := ⟨unaryFamilyBasePoint p.val,hBase p.val p.property⟩
    have hHead : p.val.1 0=q.val.1 0 := hOther 0 (Fin.succ_ne_zero T.coordinate).symm
    have hBq : unaryFamilyBasePoint q.val=b.val := by
      apply Prod.ext
      · funext i
        exact hHead.symm
      · exact (congrArg (fun u => u ∘ Fin.castAdd s) hTags).symm
    let a := unaryFamilyParameter η b
    have ha : a ∈ T.good A P := hGood p.val p.property.1 b rfl
    let g := rvFamilyMap (focusActive (A.fibre a) (T.active.fibre a)) (T.focus.value a ha.1.1.1)
      (T.focus.family_graph_definable a ha.1.1.1)
    have hGraph := focusGraphParameterCode_at A T.active T.focus a ha.1.1.1
    have hIndependent := (mem_focusIndependentParameterLocus_map_iff
      (focusGraphParameterCode A T.active T.focus) a T.coordinate g hGraph).mp ha.2.1.1.2
    have hpA := (mem_unaryIndexedMixedFamily_at η A p.val b rfl).mp (hW p.property.1)
    have hqA := (mem_unaryIndexedMixedFamily_at η A q.val b hBq).mp (hW q.property.1)
    have hpU := (hLocus p.val p.property.1 b rfl).mp p.property.2
    have hqU := (hLocus q.val q.property.1 b hBq).mp q.property.2
    have hLocal := hIndependent ⟨(Fin.tail p.val.1,p.val.2 ∘ Fin.natAdd r),hpA,hpU⟩
      ⟨(Fin.tail q.val.1,q.val.2 ∘ Fin.natAdd r),hqA,hqU⟩
      (congrArg (fun u => u ∘ Fin.natAdd r) hTags)
      (fun i hi => hOther i.succ (fun he => hi (Fin.succ_injective _ he)))
    change (unaryIndexedFamilyMap η T.focus C hBase hFGood p).val 0=
      (unaryIndexedFamilyMap η T.focus C hBase hFGood q).val 0
    rw [unaryIndexedFamilyMap_value η T.focus C hBase hFGood p b rfl,
      unaryIndexedFamilyMap_value η T.focus C hBase hFGood q b hBq]
    simpa only [g,rvFamilyMap,a] using hLocal
  · intro p
    let b : B := ⟨unaryFamilyBasePoint p.val,hBase p.val p.property⟩
    let a := unaryFamilyParameter η b
    have ha : a ∈ T.good A P := hGood p.val p.property.1 b rfl
    let g := rvFamilyMap (focusActive (A.fibre a) (T.active.fibre a)) (T.focus.value a ha.1.1.1)
      (T.focus.family_graph_definable a ha.1.1.1)
    have hGraph := focusGraphParameterCode_at A T.active T.focus a ha.1.1.1
    have hLeading := (mem_focusLeadingTermParameterLocus_map_iff
      (focusGraphParameterCode A T.active T.focus) a T.coordinate g hGraph).mp ha.2.1.2
    have hpA := (mem_unaryIndexedMixedFamily_at η A p.val b rfl).mp (hW p.property.1)
    have hpU := (hLocus p.val p.property.1 b rfl).mp p.property.2
    have h := hLeading ⟨(Fin.tail p.val.1,p.val.2 ∘ Fin.natAdd r),hpA,hpU⟩
    change rv M ((unaryIndexedFamilyMap η T.focus C hBase hFGood p).val 0)=
      rv M (p.val.1 T.coordinate.succ)
    rw [unaryIndexedFamilyMap_value η T.focus C hBase hFGood p b rfl]
    exact h

end DiamondIntegral.Section6
