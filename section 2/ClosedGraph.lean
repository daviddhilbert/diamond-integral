import «section 2».ClosedGraphCriterion

/-! Lemma 2.50 in the manuscript's actual relative projective target. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def projectiveTarget (B : Set (Fin m → VF M)) : Set (Fin m → ProjectiveLine (VF M)) :=
  closure (finiteProjectiveTuple '' B)

def compactifiedTargetGraph (A : Set (Fin n → VF M)) (B : Set (Fin m → VF M))
    (f : (Fin n → VF M) → Fin m → VF M) : Set (A × projectiveTarget B) :=
  {p | p.2.val = finiteProjectiveTuple (f p.1.val)}

theorem compactifiedTargetGraph_isClosed_iff
    (A : Set (Fin n → VF M)) (B : Set (Fin m → VF M))
    (f : (Fin n → VF M) → Fin m → VF M) (hfB : Set.MapsTo f A B) :
    IsClosed (compactifiedTargetGraph A B f) ↔ IsClosed (relativeProjectiveGraph A f) := by
  let j : A × projectiveTarget B → A × (Fin m → ProjectiveLine (VF M)) := Prod.map id Subtype.val
  have hj : IsClosedEmbedding j := IsClosedEmbedding.id.prodMap
    (IsClosedEmbedding.subtypeVal isClosed_closure)
  have he : j '' compactifiedTargetGraph A B f = relativeProjectiveGraph A f := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact hq
    · intro hp
      have hmem : p.2 ∈ projectiveTarget B := by
        rw [hp]
        exact subset_closure ⟨f p.1.val,hfB p.1.property,rfl⟩
      exact ⟨(p.1,⟨p.2,hmem⟩),hp,rfl⟩
  have h := hj.isClosed_iff_image_isClosed (s := compactifiedTargetGraph A B f)
  rw [he] at h
  exact h

/-- Lemma 2.50. The graph is closed in A times the projective closure
of B. The original real parameter base need not be VF-generated. -/
theorem lemma_2_50
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (B : Set (Fin m → VF M)) (hB : S.Definable LRV (vfValues '' B)) (hBcl : IsClosed B)
    (f : (Fin n → VF M) → Fin m → VF M) (hfB : Set.MapsTo f A B)
    (hf : S.Definable LRV (vfCorrespondenceGraph A (fun x => {f x}))) :
    ContinuousOn f A ↔ IsClosed (compactifiedTargetGraph A B f) := by
  rw [compactifiedTargetGraph_isClosed_iff A B f hfB]
  exact continuousOn_iff_relativeProjectiveGraph_isClosed h00 hc hκ hs hv A f hf

theorem projectiveClosure_eq_finite_of_closed_bounded
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (B : Set (Fin m → VF M)) (hBcl : IsClosed B)
    (hBb : ∃ γ : Gamma M, ∀ x ∈ B, ∀ i, γ.val ≤ vfValue (x i)) :
    projectiveTarget B = finiteProjectiveTuple '' B := by
  ext p
  constructor
  · intro hp
    let b : Fin m → LimitPoint M := fun i => (p i).point
    have hpb : projectiveTuple b = p := rfl
    have hb : projectiveClosure B b := (projectiveClosure_iff_topological hv B b).mpr (hpb.symm ▸ hp)
    obtain ⟨γ,hγ⟩ := hBb
    have hfinite : ∀ i, ∃ x, b i = some x := by
      intro i
      cases hi : b i with
      | some x => exact ⟨x,rfl⟩
      | none =>
        obtain ⟨x,hx,hnear⟩ := hb γ⁻¹
        have hi' := hnear i
        rw [hi] at hi'
        change vfValue (x i) < (γ⁻¹⁻¹).val at hi'
        have hsmall : vfValue (x i) < γ.val := by
          simpa only [inv_inv] using hi'
        exact False.elim ((not_lt_of_ge (hγ x hx i)) hsmall)
    have he : b = finiteLimitPoint (projectiveCentre b) := by
      funext i
      obtain ⟨x,hx⟩ := hfinite i
      simp only [projectiveCentre,finiteLimitPoint,hx,Option.getD_some]
    have hcB : projectiveCentre b ∈ B := by
      rw [← hBcl.closure_eq]
      exact (projectiveClosure_finite_iff hv B (projectiveCentre b)).mp (he ▸ hb)
    refine ⟨projectiveCentre b,hcB,?_⟩
    rw [← hpb,he]
    rfl
  · exact fun hp => subset_closure hp

end DiamondIntegral.Section2
