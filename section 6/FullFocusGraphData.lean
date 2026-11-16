import «section 6».UniformProtectedCovarianceData

/-! Actual full-domain focus graphs, without a prior choice of a
global complementary-coordinate formula. Independence on the active
coordinate reconstructs that formula on the precise current domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure FullFocusGraphData (A : DefSet (rawMixedSpace (M := M) n r) S) where
  coordinate : Fin n
  activeTags : DefSet (rawRVSpace (M := M) r) S
  map : Map (focusActive A activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S)
  independent : ∀ p q : focusActive A activeTags,p.val.2=q.val.2 →
    (∀ i ≠ coordinate,p.val.1 i=q.val.1 i) → (map p).val 0=(map q).val 0
  proper : ProperInvariant S A.carrier
  doublyBounded : VFDoublyBounded A.carrier
  tagged : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1
  continuous : ∀ u,Continuous (FMT.focusFibre map u)
  leadingTerm : ∀ p : focusActive A activeTags,rv M ((map p).val 0)=rv M (p.val.1 coordinate)

namespace FullFocusGraphData
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def focus (F : FullFocusGraphData (G := G) A) (x : Fin n → VF M) (u : Fin r → RVInfinity M) : VF M :=
  if h : ∃ p : focusActive A F.activeTags,p.val.2=u ∧ ∀ i ≠ F.coordinate,p.val.1 i=x i then
    (F.map h.choose).val 0 else 0

theorem focus_at (F : FullFocusGraphData (G := G) A) (p : focusActive A F.activeTags) :
    F.focus (Function.update p.val.1 F.coordinate 0) p.val.2=(F.map p).val 0 := by
  have h : ∃ q : focusActive A F.activeTags,q.val.2=p.val.2 ∧
      ∀ i ≠ F.coordinate,q.val.1 i=Function.update p.val.1 F.coordinate 0 i :=
    ⟨p,rfl,fun i hi => (Function.update_of_ne hi 0 p.val.1).symm⟩
  rw [focus,dif_pos h]
  apply F.independent h.choose p h.choose_spec.1
  intro i hi
  exact (h.choose_spec.2 i hi).trans (Function.update_of_ne hi 0 p.val.1)

theorem focus_continuousOn (F : FullFocusGraphData (G := G) A)
    (u : Fin r → RVInfinity M) (hu : u ∈ F.activeTags.carrier) :
    ContinuousOn (fun x : Fin n → VF M => F.focus (Function.update x F.coordinate 0) u)
      (vfFibre A.carrier u) := by
  let g : vfFibre A.carrier u → vfFibre (focusActive A F.activeTags).carrier u :=
    fun p => ⟨p.val,p.property,hu⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk (fun p => ⟨p.property,hu⟩)
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert (F.continuous u).comp hg using 1
  funext p
  exact F.focus_at ⟨(p.val,u),p.property,hu⟩

end FullFocusGraphData

def CentripetalData.fullFocusGraph {A : DefSet (rawMixedSpace (M := M) n r) S}
    (D : CentripetalData (G := G) A) : FullFocusGraphData (G := G) A where
  coordinate := D.coordinate
  activeTags := D.activeTags
  map := D.focusMap
  independent p q hTags hOther := by
    rw [D.focusMap_eq p,D.focusMap_eq q,hTags]
    apply congrArg (fun x => D.focus x q.val.2)
    funext i
    by_cases hi : i=D.coordinate
    · subst i
      simp only [Function.update_self]
    · simpa only [Function.update_of_ne hi] using hOther i hi
  proper := D.sourceProper
  doublyBounded := D.sourceDoublyBounded
  tagged := D.tagged
  continuous := D.focusMap_continuous
  leadingTerm p := by
    rw [D.focusMap_eq p]
    exact D.focusRV p.val p.property.1 p.property.2

end DiamondIntegral.Section6
