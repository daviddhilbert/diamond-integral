import «section 5».VarietySubsetObjects
import «section 5».ReducedImmersionRangeProperties
import «section 5».LocallyClosedScissorAdditivity

/-! Classes of invariant locally closed subsets satisfy actual closed/open
scissors in the geometric variety ring. Their finite partition formula
therefore follows from those defining relations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory TopologicalSpace Topology
attribute [local instance] Object.reduced

theorem Object.Invariant.empty (X : Object) : X.Invariant ∅ := fun _ _ => Iff.rfl

theorem Object.Invariant.univ (X : Object) : X.Invariant Set.univ := fun _ _ => Iff.rfl

theorem Object.Invariant.inter {X : Object} {S T : Set X.scheme}
    (hS : X.Invariant S) (hT : X.Invariant T) : X.Invariant (S ∩ T) :=
  fun h x => and_congr (hS h x) (hT h x)

theorem Object.Invariant.sdiff {X : Object} {S T : Set X.scheme}
    (hS : X.Invariant S) (hT : X.Invariant T) : X.Invariant (S \ T) :=
  fun h x => and_congr (hS h x) (not_congr (hT h x))

theorem Object.Invariant.closure {X : Object} {S : Set X.scheme}
    (hS : X.Invariant S) : X.Invariant (closure S) := by
  intro h x
  let e := Scheme.homeoOfIso (X.action h).asIso
  have he : e ⁻¹' S = S := Set.ext (hS h)
  have hc := e.preimage_closure S
  rw [he] at hc
  exact Set.ext_iff.mp hc x

def subsetClass (X : Object) (S : Set X.scheme) : Ring :=
  if h : IsLocallyClosed S ∧ X.Invariant S then objectClass (subsetObject X S h.1 h.2) else 0

theorem subsetClass_of_locallyClosed (X : Object) (S : Set X.scheme)
    (hS : IsLocallyClosed S) (hiS : X.Invariant S) :
    subsetClass X S = objectClass (subsetObject X S hS hiS) := by
  exact dif_pos (show IsLocallyClosed S ∧ X.Invariant S from ⟨hS, hiS⟩)

theorem subsetClass_empty (X : Object) : subsetClass X ∅ = 0 := by
  rw [subsetClass_of_locallyClosed X ∅ isClosed_empty.isLocallyClosed (Object.Invariant.empty X)]
  apply objectClass_empty
  exact ⟨fun x => by
    have hx := (subsetInclusion_range X ∅ isClosed_empty.isLocallyClosed (Object.Invariant.empty X)).subset
      ⟨x, rfl⟩
    exact hx⟩

theorem subsetClass_univ (X : Object) : subsetClass X Set.univ = objectClass X := by
  rw [subsetClass_of_locallyClosed X Set.univ isClosed_univ.isLocallyClosed (Object.Invariant.univ X)]
  let f := subsetInclusion X Set.univ isClosed_univ.isLocallyClosed (Object.Invariant.univ X)
  letI := subsetInclusion_immersion X Set.univ isClosed_univ.isLocallyClosed (Object.Invariant.univ X)
  let g : Morphism X X := ⟨𝟙 _, Category.id_comp _, fun _ => by simp⟩
  exact objectClass_immersed_presentations f g (by
    rw [subsetInclusion_range]
    exact (Set.range_id).symm)

theorem subsetClass_split (X : Object) (S Z : Set X.scheme)
    (hS : IsLocallyClosed S) (hiS : X.Invariant S) (hZ : IsClosed Z) (hiZ : X.Invariant Z) :
    subsetClass X S = subsetClass X (S ∩ Z) + subsetClass X (S \ Z) := by
  have hC : IsLocallyClosed (S ∩ Z) := hS.inter hZ.isLocallyClosed
  have hU : IsLocallyClosed (S \ Z) := hS.inter hZ.isOpen_compl.isLocallyClosed
  let hiC := hiS.inter hiZ
  let hiU := hiS.sdiff hiZ
  let i := subsetMorphism X hC hS hiC hiS Set.inter_subset_left
  let j := subsetMorphism X hU hS hiU hiS Set.sdiff_subset
  let b := (subsetInclusion X S hS hiS).hom
  letI := subsetMorphism_immersion X hC hS hiC hiS Set.inter_subset_left
  letI := subsetMorphism_immersion X hU hS hiU hiS Set.sdiff_subset
  have hrC : Set.range i.hom = b ⁻¹' Z := by
    rw [subsetMorphism_range]
    ext x
    have hx : b x ∈ S := (subsetInclusion_range X S hS hiS).subset ⟨x, rfl⟩
    exact and_iff_right hx
  have hrU : Set.range j.hom = b ⁻¹' Zᶜ := by
    rw [subsetMorphism_range]
    ext x
    have hx : b x ∈ S := (subsetInclusion_range X S hS hiS).subset ⟨x, rfl⟩
    exact and_iff_right hx
  have hc : IsClosedImmersion i.hom := reduced_immersion_closed_of_range i.hom (by
    rw [hrC]
    exact hZ.preimage b.continuous)
  have hu : IsOpenImmersion j.hom := reduced_immersion_open_of_range j.hom (by
    rw [hrU]
    exact hZ.isOpen_compl.preimage b.continuous)
  rw [subsetClass_of_locallyClosed X S hS hiS,
    subsetClass_of_locallyClosed X (S ∩ Z) hC hiC,
    subsetClass_of_locallyClosed X (S \ Z) hU hiU]
  exact objectClass_scissor _ _ _ i j hc hu (by rw [hrC, hrU]; rfl)

def geometricScissorFunction (X : Object) : LocallyClosedScissorFunction X.scheme Ring where
  admissible := X.Invariant
  empty_admissible := Object.Invariant.empty X
  inter_admissible := Object.Invariant.inter
  sdiff_admissible := Object.Invariant.sdiff
  closure_admissible := Object.Invariant.closure
  value := subsetClass X
  empty := subsetClass_empty X
  split := subsetClass_split X

theorem subsetClass_finite_partition (X : Object) {ι : Type*} [Fintype ι]
    (D : ι → Set X.scheme) (hD : ∀ i, IsLocallyClosed (D i))
    (hiD : ∀ i, X.Invariant (D i))
    (hdisj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hcov : ∀ x : X.scheme, ∃ i, x ∈ D i) :
    objectClass X = ∑ i, subsetClass X (D i) := by
  rw [← subsetClass_univ X]
  exact finite_locallyClosed_scissor_partition (geometricScissorFunction X) Finset.univ Set.univ D
    isClosed_univ.isLocallyClosed (Object.Invariant.univ X)
    (fun i _ => hD i) (fun i _ => hiD i) (fun _ _ => Set.subset_univ _)
    (fun i _ j _ hne => hdisj hne) (fun x _ => by
      obtain ⟨i, hi⟩ := hcov x
      exact ⟨i, Finset.mem_univ i, hi⟩)

end DiamondIntegral.Section5.EquivariantVariety
