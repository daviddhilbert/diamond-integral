import «section 6».PairedCenteredDiscs
import «section 6».ProperHomeomorphisms

/-! The actual scalar maps on fixed old source and target RV labels.
Their complete partial graphs and bijections are derived from the
original mixed map, rather than supplied as new scalar inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem scalarGraphFibre_tuple_eta (x : Fin 1 → VF M) : (fun _ : Fin 1 => x 0)=x := by
  funext i
  fin_cases i
  rfl

def unaryGraphFibreSource (f : Map A B) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) : Set (VF M) :=
  {x | (fun _ : Fin 1 => x) ∈ graphFibreSource f u v}

def unaryGraphFibreRange (f : Map A B) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) : Set (VF M) :=
  {y | (fun _ : Fin 1 => y) ∈ graphFibreRange f u v}

def unaryGraphFibreMap (f : Map A B) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) (x : VF M) : VF M :=
  graphFibreMap f u v (fun _ : Fin 1 => x) 0

theorem unaryGraphFibreMap_graph_definable (f : Map A B)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    (graphFibreBase S u v).Definable LRV
      (scalarPartialGraph (unaryGraphFibreSource f u v) (unaryGraphFibreMap f u v)) := by
  let idx : Fin 1 ⊕ Fin 1 → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)
  have h := (graphFibreMap_definable f u v).preimage_comp idx
  convert h using 1
  ext z
  constructor
  · rintro ⟨x,hx,hxz,hyz⟩
    refine ⟨fun _ : Fin 1 => x,hx,graphFibreMap f u v (fun _ => x),Set.mem_singleton _,?_⟩
    funext i
    cases i with
    | inl i => fin_cases i; exact hxz
    | inr i => fin_cases i; exact hyz
  · rintro ⟨a,ha,b,hb,he⟩
    have hb' : b=graphFibreMap f u v a := Set.mem_singleton_iff.mp hb
    subst b
    refine ⟨a 0,?_,congrFun he (.inl 0),?_⟩
    · change (fun _ : Fin 1 => a 0) ∈ graphFibreSource f u v
      rw [scalarGraphFibre_tuple_eta]
      exact ha
    · change (graphFibreMap f u v (fun _ : Fin 1 => a 0) 0).val=z 1
      rw [scalarGraphFibre_tuple_eta]
      exact congrFun he (.inr 0)

theorem unaryGraphFibreMap_bijOn (f : Map A B) (hf : Function.Injective f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    Set.BijOn (unaryGraphFibreMap f u v) (unaryGraphFibreSource f u v) (unaryGraphFibreRange f u v) := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    have h := graphFibreMap_graph f u v hx
    change (fun _ : Fin 1 => graphFibreMap f u v (fun _ : Fin 1 => x) 0) ∈ graphFibreRange f u v
    rw [scalarGraphFibre_tuple_eta]
    exact ⟨_,h⟩
  · intro x hx y hy he
    have hTuples : graphFibreMap f u v (fun _ : Fin 1 => x)=graphFibreMap f u v (fun _ : Fin 1 => y) := by
      funext i
      fin_cases i
      exact he
    exact congrFun (graphFibreMap_injOn f hf u v hx hy hTuples) 0
  · intro y hy
    obtain ⟨a,ha⟩ := hy
    have hSource : a ∈ graphFibreSource f u v := ⟨_,ha⟩
    refine ⟨a 0,?_,?_⟩
    · change (fun _ : Fin 1 => a 0) ∈ graphFibreSource f u v
      rw [scalarGraphFibre_tuple_eta]
      exact hSource
    · change graphFibreMap f u v (fun _ : Fin 1 => a 0) 0=y
      rw [scalarGraphFibre_tuple_eta]
      exact congrFun (graphFibre_functional f u v (graphFibreMap_graph f u v hSource) ha) 0

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem unaryGraphFibreMap_continuous (f : Map A B) (h : ContinuousOnGraphFibres f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    ContinuousOn (unaryGraphFibreMap f u v) (unaryGraphFibreSource f u v) := by
  have hTuple : Continuous (fun x : VF M => fun _ : Fin 1 => x) := continuous_pi (fun _ => continuous_id)
  exact (continuous_apply 0).comp_continuousOn ((h u v).comp hTuple.continuousOn (fun _ hx => hx))

theorem unaryGraphFibreSource_open
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (h : ProperCovariant f) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    IsOpen (unaryGraphFibreSource f u v) := by
  obtain ⟨α,β,hα,hβ,hSource,hRange,hCov⟩ := h.radii u v
  exact (hSource.isClopen hv).isOpen.preimage (continuous_pi (fun _ => continuous_id))

theorem unaryGraphFibreRange_bounded (f : Map A B) (h : VFBounded (mixedMapRange f))
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    ∃ η : Gamma M,∀ y ∈ unaryGraphFibreRange f u v,η.val ≤ vfValue y := by
  obtain ⟨η,hη⟩ := h
  refine ⟨η,?_⟩
  rintro y ⟨x,p,hp,hfp⟩
  have hVal := hη (f p).val ⟨p,rfl⟩ 0
  rw [hfp] at hVal
  exact hVal

end DiamondIntegral.Section6
