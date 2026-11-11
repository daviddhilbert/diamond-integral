import «section 2».FibreBadLocus
import «section 2».UnaryInterior
import «section 2».CorrespondenceSets

/-! Finite-valued continuity cannot choose bad-locus points with one
uniform fibre radius throughout an open unary base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem vf_open_nonempty_infinite
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {k : ℕ} (hk : 0 < k) (U : Set (Fin k → VF M)) (hU : IsOpen U) (hne : U.Nonempty) :
    U.Infinite := by
  intro hfin
  obtain ⟨a,ha⟩ := hne
  have hdel : (U \ {a}).Finite := hfin.subset Set.sdiff_subset
  have hnot : a ∈ (U \ {a})ᶜ := fun h => h.2 rfl
  have hN := Filter.inter_mem (hU.mem_nhds ha) (hdel.isClosed.isOpen_compl.mem_nhds hnot)
  obtain ⟨δ,hδ⟩ := exists_vfBall_subset_nhds hv a hN
  obtain ⟨x,hx,hxa⟩ := exists_ne_mem_vfBall a δ hk
  have h := hδ hx
  exact h.2 ⟨h.1,hxa⟩

theorem fibreBallHits_finite
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (I D : Set (Fin 1 → VF M)) (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (F : (Fin 1 → VF M) → Set (Fin n → VF M)) (γ : Gamma M)
    {S : Set M} (hG : S.Definable LRV (vfCorrespondenceGraph D F))
    (hF : ∀ a ∈ D, ∀ x ∈ F a,
      (a,x) ∈ relativeBadLocus (I ×ˢ Set.univ) A ∧ ∀ y ∈ vfBall x γ, (a,y) ∈ A)
    (e : Fin n → VF M) : (fibreBallHits D F e γ).Finite := by
  have hJ : (Set.univ : Set M).Definable LRV (vfValues '' fibreBallHits D F e γ) :=
    vfCorrespondence_hits_definable D F (hG.mono (Set.subset_univ _)) (vfBall e γ)
      (vfBall_definable_univ hc e γ)
  exact unary_definable_finite_of_interior_empty_any_base hc hκ hs hv _ hJ
    (fibreBallHits_interior_empty hv I D A F γ hF e)

theorem no_finite_continuous_choice_in_uniform_bad_locus
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (I D : Set (Fin 1 → VF M)) (hD : IsOpen D)
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (F : (Fin 1 → VF M) → Set (Fin n → VF M)) (γ : Gamma M)
    {S : Set M} (hG : S.Definable LRV (vfCorrespondenceGraph D F))
    (hF : ∀ a ∈ D, ∀ x ∈ F a,
      (a,x) ∈ relativeBadLocus (I ×ˢ Set.univ) A ∧ ∀ y ∈ vfBall x γ, (a,y) ∈ A)
    (hne : ∀ a ∈ D, (F a).Nonempty) (a : Fin 1 → VF M) (ha : a ∈ D)
    (hfin : (F a).Finite) (hlim : HasLimitSet D a F (F a)) : False := by
  classical
  obtain ⟨δ,hδ⟩ := hlim γ
  let W := D ∩ vfBall a δ
  have hWfin : W.Finite := by
    apply (hfin.biUnion (fun e _ => fibreBallHits_finite hc hκ hs hv I D A F γ hG hF e)).subset
    intro c hcW
    obtain ⟨x,hx⟩ := hne c hcW.1
    by_cases he : c = a
    · subst c
      exact Set.mem_iUnion₂.mpr ⟨x,hx,ha,x,hx,mem_vfBall_self x γ⟩
    · obtain ⟨e,he,hxe⟩ := hδ c ⟨hcW.1,he⟩ hcW.2 x hx
      exact Set.mem_iUnion₂.mpr ⟨e,he,hcW.1,x,hx,hxe⟩
  exact vf_open_nonempty_infinite hv (by decide : 0 < 1) W
    (hD.inter (vfBall_isOpen hv a δ)) ⟨a,ha,mem_vfBall_self a δ⟩ hWfin

end DiamondIntegral.Section2
