import «section 6».InvarianceTopology
import «section 2».GammaBallRelations
import «section 2».UniformGammaSuprema
import «section 2».PartitionBoundedVF
import Section3.GammaDensity

/-! Least interior-ball radii and the bounded partition argument. All
radius formulas keep every nonzero RV code of the actual Gamma value. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem vfBall_exists_larger_radius {a x : Fin n → VF M} {γ : Gamma M}
    (hx : x ∈ vfBall a γ) : ∃ δ : Gamma M, γ < δ ∧ x ∈ vfBall a δ := by
  classical
  have hex (i : Fin n) : ∃ δ : Gamma M, γ < δ ∧ δ.val < vfValue (x i - a i) := by
    by_cases hzero : x i - a i = 0
    · obtain ⟨δ,hδ⟩ := exists_gt γ
      exact ⟨δ,hδ,by rw [hzero]; exact gamma_lt_value_zero δ⟩
    · have hg : γ < finiteValue (x i - a i) hzero := hx i
      obtain ⟨δ,hγ,hδ⟩ := exists_between hg
      exact ⟨δ,hγ,hδ⟩
  choose d hd hdv using hex
  obtain ⟨δ₀,hδ₀⟩ := exists_gt γ
  let e : Option (Fin n) → Gamma M := fun i => i.elim δ₀ d
  let δ := Finset.univ.inf' Finset.univ_nonempty e
  refine ⟨δ,?_,?_⟩
  · apply (Finset.lt_inf'_iff _).mpr
    rintro (i | i) _
    · exact hδ₀
    · exact hd i
  · intro i
    exact (show δ.val ≤ (d i).val from
      Finset.inf'_le e (Finset.mem_univ (some i))).trans_lt (hdv i)

def InteriorRadii (A : Set (Fin n → VF M)) (a : Fin n → VF M) : Set (Gamma M) :=
  {γ | (1 : Gamma M) ≤ γ ∧ vfBall a γ ⊆ A}

theorem interiorRadii_upper {A : Set (Fin n → VF M)} {a : Fin n → VF M}
    {γ δ : Gamma M} (hγ : γ ∈ InteriorRadii A a) (hγδ : γ ≤ δ) :
    δ ∈ InteriorRadii A a :=
  ⟨hγ.1.trans hγδ,fun _ hx => hγ.2 (vfBall_anti hγδ hx)⟩

theorem interiorRadii_closed {A : Set (Fin n → VF M)} (a : Fin n → VF M)
    (γ : Gamma M) (h : ∀ δ, γ < δ → δ ∈ InteriorRadii A a) :
    γ ∈ InteriorRadii A a := by
  refine ⟨?_,?_⟩
  · by_contra hn
    obtain ⟨δ,hγδ,hδ1⟩ := exists_between (lt_of_not_ge hn)
    exact (not_le_of_gt hδ1) (h δ hγδ).1
  · intro x hx
    obtain ⟨δ,hδ,hxδ⟩ := vfBall_exists_larger_radius hx
    exact (h δ hδ).2 hxδ

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem interiorRadii_nonempty
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Set (Fin n → VF M)} (hA : IsOpen A) {a : Fin n → VF M} (ha : a ∈ A) :
    (InteriorRadii A a).Nonempty := by
  obtain ⟨γ,hγ⟩ := exists_vfBall_subset_nhds hv a (hA.mem_nhds ha)
  exact ⟨max 1 γ,le_max_left _ _,fun _ hx => hγ (vfBall_anti (le_max_right _ _) hx)⟩

theorem least_interior_radii_partition {A : Set (Fin n → VF M)}
    (p : (Fin n → VF M) → Gamma M)
    (hp : ∀ a ∈ A, IsLeast (InteriorRadii A a) (p a)) : IsOpenDiscPartition A p := by
  intro a ha x hx hxa
  have hpx : p x ≤ p a := (hp x hx).2 ⟨(hp a ha).1.1,fun y hy =>
    (hp a ha).1.2 (mem_vfBall_of_common_center (vfBall_symm hxa) hy)⟩
  apply le_antisymm hpx
  apply (hp a ha).2
  refine ⟨(hp x hx).1.1,fun y hy => ?_⟩
  have hax : a ∈ vfBall x (p x) := vfBall_anti hpx (vfBall_symm hxa)
  exact (hp x hx).1.2 (mem_vfBall_of_common_center (vfBall_symm hax) hy)

theorem alphaInvariant_of_bounded_interior_radii {A : Set (Fin n → VF M)}
    (p : (Fin n → VF M) → Gamma M)
    (hp : ∀ a ∈ A, vfBall a (p a) ⊆ A) (δ : Gamma M)
    (hδ : ∀ a ∈ A, p a ≤ δ) : AlphaInvariant (fun _ => δ) A := by
  intro a b hab
  constructor
  · intro ha
    exact hp a ha (vfBall_anti (hδ a ha) hab.symm)
  · intro hb
    exact hp b hb (vfBall_anti (hδ b hb) hab)

theorem clopen_invariant_of_least_radius_graph
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (hclosed : IsClosed A)
    (hbounded : ∃ γ : Gamma M, ∀ x ∈ A, ∀ i, γ.val ≤ vfValue (x i))
    (p : (Fin n → VF M) → Gamma M)
    (hp : ∀ a ∈ A, IsLeast (InteriorRadii A a) (p a))
    (hgraph : S.Definable LRV (vfGammaGraph A p)) :
    ∃ δ : Gamma M, AlphaInvariant (fun _ => δ) A := by
  obtain ⟨δ,hδ⟩ := (lemma_2_53_vf h00 hc hκ hs hv A hA hclosed hbounded p
    (least_interior_radii_partition p hp) hgraph).2
  exact ⟨δ,alphaInvariant_of_bounded_interior_radii p (fun a ha => (hp a ha).1.2) δ
    (fun a ha => hδ ⟨a,ha,rfl⟩)⟩

end DiamondIntegral.Section6
