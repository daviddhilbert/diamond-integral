import «section 6».ProperHomeomorphisms
import «section 6».RVFocusContinuity

/-! Fixed-label graph maps of a proper covariant homeomorphism extend
by zero to continuous total VF functions. Their source and range
indicators are continuous as well. These are the actual functions
used for simultaneous parameter freezing. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

theorem graphFibreMap_continuous_of_clopen
    (f : Map A B) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (hD : IsClopen (graphFibreSource f u v))
    (hCont : ContinuousOn (graphFibreMap f u v) (graphFibreSource f u v)) :
    Continuous (graphFibreMap f u v) := by
  exact continuous_of_clopen_zero_complement _ hD _ hCont (fun _ hx => dif_neg hx)

theorem ProperCovariantHomeomorphism.graphFibreMap_continuous
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {f : Map A B} (hF : ProperCovariantHomeomorphism f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    Continuous (graphFibreMap f u v) := by
  obtain ⟨α,β,hα,hβ,hD,hR,hCov⟩ := hF.covariant.radii u v
  exact graphFibreMap_continuous_of_clopen f u v (hD.isClopen hv) (hF.continuous u v)

theorem indicator_continuous_of_clopen {X : Type} [TopologicalSpace X]
    (D : Set X) (hD : IsClopen D) : Continuous (fun x : X => if x ∈ D then (1 : VF M) else 0) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  by_cases ha : a ∈ D
  · apply (continuousAt_const : ContinuousAt (fun _ : X => (1 : VF M)) a).congr_of_eventuallyEq
    filter_upwards [hD.isOpen.mem_nhds ha] with x hx
    exact if_pos hx
  · apply (continuousAt_const : ContinuousAt (fun _ : X => (0 : VF M)) a).congr_of_eventuallyEq
    filter_upwards [hD.isClosed.isOpen_compl.mem_nhds ha] with x hx
    exact if_neg hx

theorem ProperCovariantHomeomorphism.graphSourceIndicator_continuous
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {f : Map A B} (hF : ProperCovariantHomeomorphism f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    Continuous (fun a => if a ∈ graphFibreSource f u v then (1 : VF M) else 0) := by
  obtain ⟨α,β,hα,hβ,hD,hR,hCov⟩ := hF.covariant.radii u v
  exact indicator_continuous_of_clopen _ (hD.isClopen hv)

theorem ProperCovariantHomeomorphism.graphRangeIndicator_continuous
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {f : Map A B} (hF : ProperCovariantHomeomorphism f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    Continuous (fun b => if b ∈ graphFibreRange f u v then (1 : VF M) else 0) := by
  obtain ⟨α,β,hα,hβ,hD,hR,hCov⟩ := hF.covariant.radii u v
  exact indicator_continuous_of_clopen _ (hR.isClopen hv)

end DiamondIntegral.Section6
