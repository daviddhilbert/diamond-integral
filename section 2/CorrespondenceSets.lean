import «section 2».VFDefinableSets

/-! Domain restrictions, nonempty domains and hitting sets of actual
VF correspondences, retaining the full graph and original real base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k n : ℕ}

theorem vfCorrespondenceGraph_at
    (D : Set (Fin k → VF M)) (F : (Fin k → VF M) → Set (Fin n → VF M))
    (a : Fin k → VF M) (x : Fin n → VF M) :
    Sum.elim (vfValues a) (vfValues x) ∈ vfCorrespondenceGraph D F ↔ a ∈ D ∧ x ∈ F a := by
  constructor
  · rintro ⟨b,hb,y,hy,he⟩
    have hba : b = a := vfValues_injective (funext (fun i => congrFun he (.inl i)))
    have hyx : y = x := vfValues_injective (funext (fun i => congrFun he (.inr i)))
    subst b
    subst y
    exact ⟨hb,hy⟩
  · rintro ⟨ha,hx⟩
    exact ⟨a,ha,x,hx,rfl⟩

theorem vfCorrespondence_hits_definable {S : Set M}
    (D : Set (Fin k → VF M)) (F : (Fin k → VF M) → Set (Fin n → VF M))
    (hF : S.Definable LRV (vfCorrespondenceGraph D F))
    (B : Set (Fin n → VF M)) (hB : S.Definable LRV (vfValues '' B)) :
    S.Definable LRV (vfValues '' {a ∈ D | ∃ x ∈ F a, x ∈ B}) := by
  have h := (hF.inter (hB.preimage_comp (Sum.inr : Fin n → Fin k ⊕ Fin n))).image_comp
    (Sum.inl : Fin k → Fin k ⊕ Fin n)
  convert h using 1
  ext z
  constructor
  · rintro ⟨a,⟨ha,x,hx,hxB⟩,rfl⟩
    exact ⟨Sum.elim (vfValues a) (vfValues x),⟨⟨a,ha,x,hx,rfl⟩,x,hxB,rfl⟩,rfl⟩
  · rintro ⟨w,⟨⟨a,ha,x,hx,he⟩,y,hy,hye⟩,hw⟩
    have hxy : x = y := vfValues_injective (funext (fun i =>
      (congrFun he (.inr i)).trans (congrFun hye i).symm))
    exact ⟨a,⟨ha,x,hx,hxy.symm ▸ hy⟩,
      funext (fun i => (congrFun he (.inl i)).trans (congrFun hw i))⟩

theorem vfCorrespondence_domain_definable {S : Set M}
    (D : Set (Fin k → VF M)) (F : (Fin k → VF M) → Set (Fin n → VF M))
    (hF : S.Definable LRV (vfCorrespondenceGraph D F)) (hne : ∀ a ∈ D, (F a).Nonempty) :
    S.Definable LRV (vfValues '' D) := by
  have h := vfCorrespondence_hits_definable D F hF Set.univ (vf_univ_definable S)
  have he : {a ∈ D | ∃ x ∈ F a, x ∈ Set.univ} = D := by
    ext a
    constructor
    · exact fun h => h.1
    · intro ha
      obtain ⟨x,hx⟩ := hne a ha
      exact ⟨ha,x,hx,Set.mem_univ _⟩
  rwa [he] at h

theorem vfCorrespondence_restrict_definable {S : Set M}
    (D C : Set (Fin k → VF M)) (hCD : C ⊆ D) (hC : S.Definable LRV (vfValues '' C))
    (F : (Fin k → VF M) → Set (Fin n → VF M))
    (hF : S.Definable LRV (vfCorrespondenceGraph D F)) :
    S.Definable LRV (vfCorrespondenceGraph C F) := by
  have h := hF.inter (hC.preimage_comp (Sum.inl : Fin k → Fin k ⊕ Fin n))
  convert h using 1
  ext z
  constructor
  · rintro ⟨a,ha,x,hx,rfl⟩
    exact ⟨⟨a,hCD ha,x,hx,rfl⟩,a,ha,rfl⟩
  · rintro ⟨⟨a,ha,x,hx,he⟩,c,hc,hce⟩
    have hca : c = a := vfValues_injective (funext (fun i =>
      (congrFun hce i).trans (congrFun he (.inl i)).symm))
    exact ⟨a,hca ▸ hc,x,hx,he⟩

end DiamondIntegral.Section2
