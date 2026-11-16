import «section 6».DefinableInvariance
import «section 2».FiniteBranchLimits

/-! The topological direction of the clopen criterion, including zero VF
arity, and gluing over invariant label fibers. No definable compactness
or uniform-radius selection is assumed for these implications. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem congruent_ball_mem_nhds
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (α : Fin n → Gamma M) (a : Fin n → VF M) :
    {b | Congruent α a b} ∈ 𝓝 a := by
  obtain ⟨δ,hδ⟩ := (Set.finite_range α).bddAbove
  apply Filter.mem_of_superset (vfBall_mem_nhds hv a δ)
  intro b hb i
  change (α i).val < Values.vfValueHom (a i - b i)
  rw [vfValue_sub_comm]
  exact (show (α i).val ≤ δ.val from hδ (Set.mem_range_self i)).trans_lt (hb i)

theorem AlphaInvariant.isOpen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {α : Fin n → Gamma M} {A : Set (Fin n → VF M)} (hA : AlphaInvariant α A) :
    IsOpen A := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  exact Filter.mem_of_superset (congruent_ball_mem_nhds hv α a)
    (fun b hb => (hA a b hb).mp ha)

theorem AlphaInvariant.isClopen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {α : Fin n → Gamma M} {A : Set (Fin n → VF M)} (hA : AlphaInvariant α A) :
    IsClopen A := by
  have hc : AlphaInvariant α Aᶜ := fun a b hab => not_congr (hA a b hab)
  exact ⟨isOpen_compl_iff.mp (hc.isOpen hv),hA.isOpen hv⟩

theorem ProperInvariantGeometry.clopen_fibres
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Set (Mixed M n m)} (hA : ProperInvariantGeometry A)
    (t : Fin m → RVInfinity M) : IsClopen (vfFibre A t) := by
  obtain ⟨α,hα⟩ := hA.fibers t
  exact hα.isClopen hv

theorem ProperInvariant.clopen_fibres
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} {A : Set (Mixed M n m)} (hA : ProperInvariant S A)
    (t : Fin m → RVInfinity M) : IsClopen (vfFibre A t) :=
  hA.geometry.clopen_fibres hv t

end DiamondIntegral.Section6
