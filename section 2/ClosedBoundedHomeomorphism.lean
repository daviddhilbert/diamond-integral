import «section 2».VFDefinableSets

/-!
# Corollary 2.49: a homeomorphism onto the image

Images of the closed bounded definable cuts A minus an open ball are
closed by Lemma 2.48. Their complements give inverse neighbourhoods.
No closed-image assertion for arbitrary nondefinable cuts is assumed.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem corollary_2_49
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A)) (hAcl : IsClosed A)
    (hAb : ∃ γ : Gamma M, ∀ x ∈ A, ∀ i, γ.val ≤ vfValue (x i))
    (f : (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (vfCorrespondenceGraph A (fun x => {f x}))) (hfcont : ContinuousOn f A)
    (hinj : Set.InjOn f A) :
    ∃ H : A ≃ₜ (f '' A), ∀ x : A, (H x).val = f x.val := by
  classical
  let g (x : A) : f '' A := ⟨f x.val,x.val,x.property,rfl⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y h
      exact Subtype.ext (hinj x.property y.property (congrArg Subtype.val h))
    · rintro ⟨y,x,hx,hxy⟩
      exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  let e : A ≃ (f '' A) := Equiv.ofBijective g hg
  have he (x : A) : (e x).val = f x.val := rfl
  have hsymm (y : f '' A) : f (e.symm y).val = y.val :=
    congrArg Subtype.val (e.apply_symm_apply y)
  have hforward : Continuous e := by
    exact (continuousOn_iff_continuous_domRestrict.mp hfcont).subtype_mk
      (fun x => ⟨x.val,x.property,rfl⟩)
  have hinverseValue : Continuous (fun y : f '' A => (e.symm y).val) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    apply tendsto_def.mpr
    intro V hV
    let a := (e.symm y).val
    obtain ⟨δ,hδ⟩ := exists_vfBall_subset_nhds hv a hV
    let C := A \ vfBall a δ
    have hCA : C ⊆ A := Set.sdiff_subset
    have hCdef : (Set.univ : Set M).Definable LRV (vfValues '' C) :=
      vf_sdiff_definable A (vfBall a δ) (hA.mono (Set.subset_univ S)) (vfBall_definable_univ hc a δ)
    have hCclosed : IsClosed C := hAcl.sdiff (vfBall_isOpen hv a δ)
    have hCbound : ∃ γ : Gamma M, ∀ x ∈ C, ∀ i, γ.val ≤ vfValue (x i) := by
      obtain ⟨γ,hγ⟩ := hAb
      exact ⟨γ,fun x hx i => hγ x hx.1 i⟩
    have hfC := vf_map_restrict_definable A C hCA hCdef f (hf.mono (Set.subset_univ S))
    have hclosed : IsClosed (f '' C) :=
      (lemma_2_48 h00 hc hκ hs hv C hCdef hCclosed hCbound f hfC (hfcont.mono hCA)).1
    have hyNot : y.val ∉ f '' C := by
      rintro ⟨x,⟨hx,hxNot⟩,hxy⟩
      have hxa : x = a := hinj hx (e.symm y).property (hxy.trans (hsymm y).symm)
      exact hxNot (hxa.symm ▸ mem_vfBall_self a δ)
    have hsubtype : ContinuousAt (Subtype.val : (f '' A) → Fin m → VF M) y :=
      continuous_subtype_val.continuousAt
    have hN : (Subtype.val : (f '' A) → Fin m → VF M) ⁻¹' (f '' C)ᶜ ∈ 𝓝 y :=
      hsubtype.preimage_mem_nhds (hclosed.isOpen_compl.mem_nhds hyNot)
    apply Filter.mem_of_superset hN
    intro z hz
    apply hδ
    by_contra hNot
    exact hz ⟨(e.symm z).val,⟨(e.symm z).property,hNot⟩,hsymm z⟩
  have hinverse : Continuous e.symm := hinverseValue.subtype_mk (fun y => (e.symm y).property)
  exact ⟨{ toEquiv := e, continuous_toFun := hforward, continuous_invFun := hinverse },he⟩

end DiamondIntegral.Section2
