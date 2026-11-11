import «section 2».ClosedGraphCriterion
import «section 2».VFPairClosure
import Mathlib.Topology.Homeomorph.Lemmas

/-! Lemma 2.50 transported to the unary-base/tail source coordinates
used in Proposition 2.55. The full map graph retains its original base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def vfPairMapGraph (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin m → VF M) :
    Set ((Fin 1 ⊕ Fin n) ⊕ Fin m → M) :=
  {z | ∃ p ∈ A, Sum.elim (vfPairValues p) (vfValues (f p)) = z}

def relativePairProjectiveGraph (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin m → VF M) :
    Set (A × (Fin m → ProjectiveLine (VF M))) :=
  {p | p.2 = finiteProjectiveTuple (f p.1.val)}

theorem vfPairMapGraph_join_definable {S : Set M}
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin m → VF M)
    (hf : S.Definable LRV (vfPairMapGraph A f)) :
    S.Definable LRV (vfCorrespondenceGraph (vfPairHomeomorph n '' A)
      (fun x => {f ((vfPairHomeomorph n).symm x)})) := by
  let e := vfPairHomeomorph (M := M) n
  let π : (Fin 1 ⊕ Fin n) ⊕ Fin m → Fin (n+1) ⊕ Fin m :=
    Sum.elim (Sum.elim (fun _ => .inl 0) (Sum.inl ∘ Fin.succ)) Sum.inr
  have h := hf.preimage_comp π
  convert h using 1
  ext z
  constructor
  · rintro ⟨_,⟨p,hp,rfl⟩,y,hy,rfl⟩
    have he : y = f p := by
      simpa only [Homeomorph.symm_apply_apply] using Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨p,hp,?_⟩
    funext i
    cases i with
    | inl i =>
      cases i with
      | inl i => fin_cases i; rfl
      | inr i => rfl
    | inr i => simp only [Function.comp_apply,π,Sum.elim_inr,Homeomorph.symm_apply_apply]
  · rintro ⟨p,hp,he⟩
    refine ⟨e p,⟨p,hp,rfl⟩,f p,?_,?_⟩
    · change f p ∈ {f (e.symm (e p))}
      rw [e.symm_apply_apply]
      exact Set.mem_singleton (f p)
    · funext i
      cases i with
      | inl i =>
        refine Fin.cases (congrFun he (.inl (.inl 0)))
          (fun j => congrFun he (.inl (.inr j))) i
      | inr i => exact congrFun he (.inr i)

theorem relativePairProjectiveGraph_isClosed_iff
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin m → VF M) :
    IsClosed (relativePairProjectiveGraph A f) ↔
      IsClosed (relativeProjectiveGraph (vfPairHomeomorph n '' A)
        (fun x => f ((vfPairHomeomorph n).symm x))) := by
  let e := vfPairHomeomorph (M := M) n
  let j := (e.image A).prodCongr (Homeomorph.refl (Fin m → ProjectiveLine (VF M)))
  have he : j ⁻¹' relativeProjectiveGraph (e '' A) (fun x => f (e.symm x)) =
      relativePairProjectiveGraph A f := by
    ext p
    change p.2 = finiteProjectiveTuple (f (e.symm (e p.1.val))) ↔
      p.2 = finiteProjectiveTuple (f p.1.val)
    rw [e.symm_apply_apply]
  rw [← he]
  exact j.isClosed_preimage

theorem continuousOn_pair_iff_projective_graph_isClosed
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (f : ((Fin 1 → VF M) × (Fin n → VF M)) → Fin m → VF M)
    (hf : S.Definable LRV (vfPairMapGraph A f)) :
    ContinuousOn f A ↔ IsClosed (relativePairProjectiveGraph A f) := by
  let e := vfPairHomeomorph (M := M) n
  let g := fun x => f (e.symm x)
  have hcont : ContinuousOn f A ↔ ContinuousOn g (e '' A) := by
    constructor
    · intro h
      exact h.comp e.symm.continuous.continuousOn (by
        rintro x ⟨p,hp,rfl⟩
        simpa only [e.symm_apply_apply] using hp)
    · intro h
      have h' := h.comp e.continuous.continuousOn (Set.mapsTo_image e A)
      exact h'.congr (fun p _ => by simp only [g,Function.comp_apply,Homeomorph.symm_apply_apply])
  rw [hcont,relativePairProjectiveGraph_isClosed_iff A f]
  exact continuousOn_iff_relativeProjectiveGraph_isClosed h00 hc hκ hs hv (e '' A) g
    (vfPairMapGraph_join_definable A f hf)

end DiamondIntegral.Section2
