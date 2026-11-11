import «section 2».ClosedBoundedImages

/-! Definable VF set cuts and full map-graph restrictions used in the
homeomorphism and closed-graph arguments. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

theorem vf_sdiff_definable {S : Set M} (A B : Set (Fin n → VF M))
    (hA : S.Definable LRV (vfValues '' A)) (hB : S.Definable LRV (vfValues '' B)) :
    S.Definable LRV (vfValues '' (A \ B)) := by
  convert hA.inter hB.compl using 1
  ext z
  constructor
  · rintro ⟨x,⟨hx,hxB⟩,rfl⟩
    refine ⟨⟨x,hx,rfl⟩,?_⟩
    rintro ⟨y,hy,he⟩
    exact hxB (vfValues_injective he ▸ hy)
  · rintro ⟨⟨x,hx,rfl⟩,hno⟩
    exact ⟨x,⟨hx,fun hxB => hno ⟨x,hxB,rfl⟩⟩,rfl⟩

theorem vf_univ_definable (S : Set M) :
    S.Definable LRV (vfValues '' (Set.univ : Set (Fin n → VF M))) := by
  convert vfRawUniverse_definable S n using 1
  ext z
  constructor
  · rintro ⟨x,_,rfl⟩ i
    exact (x i).property
  · intro hz
    exact ⟨fun i => ⟨z i,hz i⟩,Set.mem_univ _,rfl⟩

theorem vf_map_preimage_definable {S : Set M}
    (A : Set (Fin n → VF M)) (f : (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (vfCorrespondenceGraph A (fun x => {f x})))
    (B : Set (Fin m → VF M)) (hB : S.Definable LRV (vfValues '' B)) :
    S.Definable LRV (vfValues '' {x ∈ A | f x ∈ B}) := by
  have h := (hf.inter (hB.preimage_comp (Sum.inr : Fin m → Fin n ⊕ Fin m))).image_comp
    (Sum.inl : Fin n → Fin n ⊕ Fin m)
  convert h using 1
  ext z
  constructor
  · rintro ⟨x,⟨hx,hfx⟩,rfl⟩
    exact ⟨Sum.elim (vfValues x) (vfValues (f x)),
      ⟨⟨x,hx,f x,Set.mem_singleton _,rfl⟩,f x,hfx,rfl⟩,rfl⟩
  · rintro ⟨w,⟨⟨x,hx,p,hp,he⟩,y,hy,hye⟩,hw⟩
    have hpy : p = y := vfValues_injective (funext (fun i =>
      (congrFun he (.inr i)).trans (congrFun hye i).symm))
    have hfx : f x ∈ B := (Set.mem_singleton_iff.mp hp) ▸ (hpy.symm ▸ hy)
    exact ⟨x,⟨hx,hfx⟩,funext (fun i => (congrFun he (.inl i)).trans (congrFun hw i))⟩

theorem vf_map_restrict_definable {S : Set M}
    (A C : Set (Fin n → VF M)) (hCA : C ⊆ A) (hC : S.Definable LRV (vfValues '' C))
    (f : (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (vfCorrespondenceGraph A (fun x => {f x}))) :
    S.Definable LRV (vfCorrespondenceGraph C (fun x => {f x})) := by
  have h := hf.inter (hC.preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin m))
  convert h using 1
  ext z
  constructor
  · rintro ⟨x,hx,y,hy,rfl⟩
    exact ⟨⟨x,hCA hx,y,hy,rfl⟩,x,hx,rfl⟩
  · rintro ⟨⟨x,hx,y,hy,he⟩,c,hc,hce⟩
    have hxe : vfValues x = z ∘ Sum.inl := funext (fun i => congrFun he (.inl i))
    have hcx := vfValues_injective (hce.trans hxe.symm)
    exact ⟨x,hcx ▸ hc,y,hy,he⟩

theorem vfBall_definable_univ (hc : CanonicalStructure.IsCanonical (M := M))
    (a : Fin n → VF M) (δ : Gamma M) :
    (Set.univ : Set M).Definable LRV (vfValues '' vfBall a δ) := by
  have h := rawLimitBall_definable (finiteLimitPoint a) δ
  rw [normalize_eq_of_isCanonical hc] at h
  simpa only [rawLimitBall,limitBall_finite] using h

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem vfBall_isOpen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin n → VF M) (δ : Gamma M) : IsOpen (vfBall a δ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact Filter.mem_of_superset (vfBall_mem_nhds hv x δ)
    (fun y hy => mem_vfBall_of_common_center (vfBall_symm hx) hy)

end DiamondIntegral.Section2
