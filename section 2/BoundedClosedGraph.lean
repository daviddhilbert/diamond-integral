import «section 2».ClosedGraph

/-! The bounded-target clause of Lemma 2.50 as an affine relative graph. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def affineTargetGraph (A : Set (Fin n → VF M)) (B : Set (Fin m → VF M))
    (f : (Fin n → VF M) → Fin m → VF M) : Set (A × B) :=
  {p | p.2.val = f p.1.val}

theorem affineTargetGraph_isClosed_iff_of_bounded
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin n → VF M)) (B : Set (Fin m → VF M)) (hBcl : IsClosed B)
    (hBb : ∃ γ : Gamma M, ∀ x ∈ B, ∀ i, γ.val ≤ vfValue (x i))
    (f : (Fin n → VF M) → Fin m → VF M) (hfB : Set.MapsTo f A B) :
    IsClosed (affineTargetGraph A B f) ↔ IsClosed (relativeProjectiveGraph A f) := by
  have hfin : IsOpenEmbedding (finiteProjectiveTuple (M := M) (n := m)) :=
    IsOpenEmbedding.piMap (fun _ => ProjectiveLine.isOpenEmbedding_finite)
  let e : B → Fin m → ProjectiveLine (VF M) := fun b => finiteProjectiveTuple b.val
  have he : IsEmbedding e := hfin.isEmbedding.comp IsEmbedding.subtypeVal
  have herange : Set.range e = finiteProjectiveTuple '' B := by
    ext p
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨b.val,b.property,rfl⟩
    · rintro ⟨b,hb,rfl⟩
      exact ⟨⟨b,hb⟩,rfl⟩
  have hecl : IsClosedEmbedding e := ⟨he,by
    rw [herange,← projectiveClosure_eq_finite_of_closed_bounded hv B hBcl hBb]
    exact isClosed_closure⟩
  let j : A × B → A × (Fin m → ProjectiveLine (VF M)) := Prod.map id e
  have hj : IsClosedEmbedding j := IsClosedEmbedding.id.prodMap hecl
  have himage : j '' affineTargetGraph A B f = relativeProjectiveGraph A f := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      change finiteProjectiveTuple q.2.val = finiteProjectiveTuple (f q.1.val)
      rw [hq]
    · intro hp
      refine ⟨(p.1,⟨f p.1.val,hfB p.1.property⟩),rfl,?_⟩
      exact Prod.ext rfl hp.symm
  have h := hj.isClosed_iff_image_isClosed (s := affineTargetGraph A B f)
  rwa [himage] at h

theorem lemma_2_50_bounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (B : Set (Fin m → VF M)) (hB : S.Definable LRV (vfValues '' B)) (hBcl : IsClosed B)
    (hBb : ∃ γ : Gamma M, ∀ x ∈ B, ∀ i, γ.val ≤ vfValue (x i))
    (f : (Fin n → VF M) → Fin m → VF M) (hfB : Set.MapsTo f A B)
    (hf : S.Definable LRV (vfCorrespondenceGraph A (fun x => {f x}))) :
    ContinuousOn f A ↔ IsClosed (affineTargetGraph A B f) := by
  rw [affineTargetGraph_isClosed_iff_of_bounded hv A B hBcl hBb f hfB]
  exact continuousOn_iff_relativeProjectiveGraph_isClosed h00 hc hκ hs hv A f hf

end DiamondIntegral.Section2
