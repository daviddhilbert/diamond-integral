import «section 6».GammaBounds

/-! Open level sets of a Gamma-valued function give a clopen equality
relation on a clopen source. No topology is placed on Gamma. The relation
is bounded in both VF blocks and retains exactly the old RV tags. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {X Y : Type*} [TopologicalSpace X]

theorem isClopen_equal_levels (A : Set X) (f : X → Y) (hA : IsClopen A)
    (hlevels : ∀ y, IsOpen {a | a ∈ A ∧ f a = y}) :
    IsClopen {p : X × X | p.1 ∈ A ∧ p.2 ∈ A ∧ f p.1 = f p.2} := by
  have hopen : IsOpen {p : X × X | p.1 ∈ A ∧ p.2 ∈ A ∧ f p.1 = f p.2} := by
    apply isOpen_iff_mem_nhds.mpr
    rintro p ⟨ha,hb,he⟩
    have hn := ((hlevels (f p.1)).prod (hlevels (f p.1))).mem_nhds ⟨⟨ha,rfl⟩,hb,he.symm⟩
    exact Filter.mem_of_superset hn (fun q hq => ⟨hq.1.1,hq.2.1,hq.1.2.trans hq.2.2.symm⟩)
  have hcomp : IsOpen {p : X × X | p.1 ∈ A ∧ p.2 ∈ A ∧ f p.1 = f p.2}ᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    by_cases ha : p.1 ∈ A
    · by_cases hb : p.2 ∈ A
      · have hne : f p.1 ≠ f p.2 := fun h => hp ⟨ha,hb,h⟩
        have hn := ((hlevels (f p.1)).prod (hlevels (f p.2))).mem_nhds ⟨⟨ha,rfl⟩,hb,rfl⟩
        apply Filter.mem_of_superset hn
        rintro q hq hR
        exact hne (hq.1.2.symm.trans (hR.2.2.trans hq.2.2))
      · have ho : IsOpen (Prod.snd ⁻¹' Aᶜ : Set (X × X)) := hA.isClosed.isOpen_compl.preimage continuous_snd
        exact Filter.mem_of_superset (ho.mem_nhds hb) (fun q hq hR => hq hR.2.1)
    · have ho : IsOpen (Prod.fst ⁻¹' Aᶜ : Set (X × X)) := hA.isClosed.isOpen_compl.preimage continuous_fst
      exact Filter.mem_of_superset (ho.mem_nhds ha) (fun q hq hR => hq hR.1)
  exact ⟨isOpen_compl_iff.mp hcomp,hopen⟩

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ}

def firstVFBlock (p : Mixed M (n+n) r) : Mixed M n r := (p.1 ∘ Fin.castAdd n,p.2)

def secondVFBlock (p : Mixed M (n+n) r) : Mixed M n r := (p.1 ∘ Fin.natAdd n,p.2)

def gammaLevelRelation (A : Set (Mixed M n r)) (f : Mixed M n r → Gamma M) : Set (Mixed M (n+n) r) :=
  {p | firstVFBlock p ∈ A ∧ secondVFBlock p ∈ A ∧ f (firstVFBlock p) = f (secondVFBlock p)}

theorem gammaLevelRelation_vfBounded {A : Set (Mixed M n r)} (hA : VFBounded A)
    (f : Mixed M n r → Gamma M) : VFBounded (gammaLevelRelation A f) := by
  obtain ⟨η,hη⟩ := hA
  refine ⟨η,?_⟩
  intro p hp i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · exact hη (firstVFBlock p) hp.1 i
  · exact hη (secondVFBlock p) hp.2.1 i

theorem gammaLevelRelation_rvBounded {A : Set (Mixed M n r)} (hA : RVSupportDoublyBounded A)
    (f : Mixed M n r → Gamma M) : RVSupportDoublyBounded (gammaLevelRelation A f) := by
  obtain ⟨η,hη⟩ := hA
  exact ⟨η,fun p hp i => hη (firstVFBlock p) hp.1 i⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem gammaLevelRelation_clopen_fibres (A : Set (Mixed M n r)) (f : Mixed M n r → Gamma M)
    (hA : ∀ u, IsClopen (vfFibre A u))
    (hlevels : ∀ u γ, IsOpen {a : Fin n → VF M | (a,u) ∈ A ∧ f (a,u) = γ})
    (u : Fin r → RVInfinity M) : IsClopen (vfFibre (gammaLevelRelation A f) u) := by
  have hcont : Continuous (fun x : Fin (n+n) → VF M => (x ∘ Fin.castAdd n,x ∘ Fin.natAdd n)) :=
    (continuous_pi (fun _ => continuous_apply _)).prodMk (continuous_pi (fun _ => continuous_apply _))
  exact (isClopen_equal_levels (vfFibre A u) (fun a => f (a,u)) (hA u) (hlevels u)).preimage hcont

end DiamondIntegral.Section6
