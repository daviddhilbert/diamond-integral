import «section 2».AffineApproach

/-!
# Pulling finite-dimensional definable families through a definable map

The map is given by its complete graph on A. Quantifying its output tuple
constructs the pulled-back family over the same base; no extension of the
map outside A, nor a choice of one preimage, is used.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k n m : ℕ}

def vfPullback (A : Set (Fin n → VF M)) (f : (Fin n → VF M) → Fin m → VF M)
    (P : (Fin k → VF M) → Set (Fin m → VF M)) (c : Fin k → VF M) : Set (Fin n → VF M) :=
  {x ∈ A | f x ∈ P c}

theorem vfPullback_graph_definable {S : Set M}
    (A : Set (Fin n → VF M)) (f : (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (vfCorrespondenceGraph A (fun x => {f x})))
    (U : Set (Fin k → VF M)) (P : (Fin k → VF M) → Set (Fin m → VF M))
    (hP : S.Definable LRV (vfCorrespondenceGraph U P)) :
    S.Definable LRV (vfCorrespondenceGraph U (vfPullback A f P)) := by
  let e : Fin n ⊕ Fin m → (Fin k ⊕ Fin n) ⊕ Fin m :=
    Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr
  let d : Fin k ⊕ Fin m → (Fin k ⊕ Fin n) ⊕ Fin m :=
    Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have h := ((hf.preimage_comp e).inter (hP.preimage_comp d)).exists_of_finite
  convert h using 1
  ext z
  change (∃ c ∈ U, ∃ x ∈ vfPullback A f P c, Sum.elim (vfValues c) (vfValues x) = z) ↔
    ∃ y : Fin m → M,
      (Sum.elim z y ∘ e ∈ vfCorrespondenceGraph A (fun x => {f x})) ∧
        (Sum.elim z y ∘ d ∈ vfCorrespondenceGraph U P)
  constructor
  · rintro ⟨c,hc,x,⟨hx,hPx⟩,rfl⟩
    refine ⟨vfValues (f x),⟨x,hx,f x,Set.mem_singleton _,?_⟩,c,hc,f x,hPx,?_⟩
    · funext i
      cases i <;> rfl
    · funext i
      cases i <;> rfl
  · rintro ⟨y,⟨x,hx,fx,hfx,he⟩,c,hc,p,hp,hpe⟩
    have hfx' : fx = f x := Set.mem_singleton_iff.mp hfx
    subst fx
    have hpf : p = f x := by
      apply vfValues_injective
      funext i
      exact (congrFun hpe (.inr i)).trans (congrFun he (.inr i)).symm
    refine ⟨c,hc,x,⟨hx,hpf ▸ hp⟩,?_⟩
    funext i
    cases i with
    | inl i => exact congrFun hpe (.inl i)
    | inr i => exact congrFun he (.inl i)

theorem vf_map_image_definable {S : Set M}
    (A : Set (Fin n → VF M)) (f : (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (vfCorrespondenceGraph A (fun x => {f x}))) :
    S.Definable LRV (vfValues '' (f '' A)) := by
  have h := hf.image_comp (Sum.inr : Fin m → Fin n ⊕ Fin m)
  convert h using 1
  ext z
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨Sum.elim (vfValues a) (vfValues (f a)),⟨a,ha,f a,Set.mem_singleton _,rfl⟩,rfl⟩
  · rintro ⟨w,⟨a,ha,p,hp,he⟩,hz⟩
    exact ⟨p,⟨a,ha,(Set.mem_singleton_iff.mp hp).symm⟩,
      funext (fun i => (congrFun he (.inr i)).trans (congrFun hz i))⟩

end DiamondIntegral.Section2
