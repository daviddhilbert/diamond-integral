import «section 2».CorrespondencePullback

/-! Full same-base graph of the image of a finite-valued correspondence
under a map defined on its actual value set. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k n m : ℕ}

theorem vfCorrespondenceGraph_image_definable {S : Set M}
    (U : Set (Fin k → VF M)) (F : (Fin k → VF M) → Set (Fin n → VF M))
    (hF : S.Definable LRV (vfCorrespondenceGraph U F))
    (A : Set (Fin n → VF M)) (hFA : ∀ c ∈ U, F c ⊆ A)
    (f : (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (vfCorrespondenceGraph A (fun x => {f x}))) :
    S.Definable LRV (vfCorrespondenceGraph U (fun c => f '' F c)) := by
  let e : Fin k ⊕ Fin n → (Fin k ⊕ Fin m) ⊕ Fin n :=
    Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  let d : Fin n ⊕ Fin m → (Fin k ⊕ Fin m) ⊕ Fin n :=
    Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)
  have h := ((hF.preimage_comp e).inter (hf.preimage_comp d)).exists_of_finite
  convert h using 1
  ext z
  change (∃ c ∈ U, ∃ y ∈ f '' F c, Sum.elim (vfValues c) (vfValues y) = z) ↔
    ∃ x : Fin n → M, Sum.elim z x ∘ e ∈ vfCorrespondenceGraph U F ∧
      Sum.elim z x ∘ d ∈ vfCorrespondenceGraph A (fun x => {f x})
  constructor
  · rintro ⟨c,hc,_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨vfValues x,⟨c,hc,x,hx,?_⟩,x,hFA c hc hx,f x,Set.mem_singleton _,?_⟩
    · funext i
      cases i <;> rfl
    · funext i
      cases i <;> rfl
  · rintro ⟨rawx,⟨c,hc,x,hx,he⟩,a,ha,y,hy,hfEq⟩
    have hxa : x = a := vfValues_injective (funext (fun i =>
      (congrFun he (.inr i)).trans (congrFun hfEq (.inl i)).symm))
    have hfy : f x = y := hxa ▸ (Set.mem_singleton_iff.mp hy).symm
    refine ⟨c,hc,y,⟨x,hx,hfy⟩,?_⟩
    funext i
    cases i with
    | inl i => exact congrFun he (.inl i)
    | inr i => exact congrFun hfEq (.inr i)

end DiamondIntegral.Section2
