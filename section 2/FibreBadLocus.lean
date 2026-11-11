import «section 2».VFDefinableSets

/-! The relative bad locus in Lemma 2.54. The geometric contradiction is
that one uniform fibre ball on an open set of base points gives an open
rectangle meeting this locus. Empty fibres and zero tail arity are allowed. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2

def relativeBadLocus {X : Type*} [TopologicalSpace X] (D A : Set X) : Set X :=
  A ∩ closure (D \ A)

theorem not_mem_relativeBadLocus_of_open {X : Type*} [TopologicalSpace X]
    (D A U : Set X) (hU : IsOpen U) (hUA : U ∩ D ⊆ A) {p : X} (hp : p ∈ U) :
    p ∉ relativeBadLocus D A := by
  intro hbad
  have hsub : D \ A ⊆ Uᶜ := by
    intro q hq hqU
    exact hq.2 (hUA ⟨hqU,hq.1⟩)
  exact (closure_minimal hsub hU.isClosed_compl hbad.2) hp

theorem open_restriction_of_bad_projection_subset
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (I E : Set X) (A : Set (X × Y)) (hAI : A ⊆ I ×ˢ Set.univ)
    (hE : Prod.fst '' relativeBadLocus (I ×ˢ Set.univ) A ⊆ E) :
    IsOpen {p : ↥(I \ E) × Y | (p.1.val,p.2) ∈ A} := by
  let j : ↥(I \ E) × Y → X × Y := Prod.map Subtype.val id
  have hj : Continuous j := continuous_subtype_val.prodMap continuous_id
  have he : {p : ↥(I \ E) × Y | (p.1.val,p.2) ∈ A} =
      j ⁻¹' (closure ((I ×ˢ Set.univ) \ A))ᶜ := by
    ext p
    constructor
    · intro hp hcl
      exact p.1.property.2 (hE ⟨j p,⟨hp,hcl⟩,rfl⟩)
    · intro hp
      by_contra hn
      exact hp (subset_closure ⟨⟨p.1.property.1,Set.mem_univ _⟩,hn⟩)
  rw [he]
  exact isClosed_closure.isOpen_compl.preimage hj

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def fibreBallHits {X : Type*} (D : Set X) (F : X → Set (Fin n → VF M))
    (e : Fin n → VF M) (γ : Gamma M) : Set X := {a ∈ D | ∃ x ∈ F a, x ∈ vfBall e γ}

theorem fibreBallHits_interior_empty
    {X : Type*} [TopologicalSpace X]
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (I D : Set X) (A : Set (X × (Fin n → VF M)))
    (F : X → Set (Fin n → VF M)) (γ : Gamma M)
    (hF : ∀ a ∈ D, ∀ x ∈ F a,
      (a,x) ∈ relativeBadLocus (I ×ˢ Set.univ) A ∧
        ∀ y ∈ vfBall x γ, (a,y) ∈ A)
    (e : Fin n → VF M) : interior (fibreBallHits D F e γ) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have haJ : a ∈ fibreBallHits D F e γ := interior_subset ha
  change a ∈ D ∧ ∃ x ∈ F a, x ∈ vfBall e γ at haJ
  obtain ⟨haD,x,hx,hxe⟩ := haJ
  let U : Set (X × (Fin n → VF M)) := interior (fibreBallHits D F e γ) ×ˢ vfBall e γ
  have hU : IsOpen U := isOpen_interior.prod (vfBall_isOpen hv e γ)
  have hUA : U ⊆ A := by
    rintro ⟨b,y⟩ ⟨hb,hy⟩
    have hbJ : b ∈ fibreBallHits D F e γ := interior_subset hb
    change b ∈ D ∧ ∃ z ∈ F b, z ∈ vfBall e γ at hbJ
    obtain ⟨hbD,z,hz,hze⟩ := hbJ
    exact (hF b hbD z hz).2 y (mem_vfBall_of_common_center hze hy)
  exact not_mem_relativeBadLocus_of_open (I ×ˢ Set.univ) A U hU (p := (a,x))
    (fun _ h => hUA h.1) ⟨ha,hxe⟩ (hF a haD x hx).1

end DiamondIntegral.Section2
