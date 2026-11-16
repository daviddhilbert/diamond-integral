import «section 6».MeasuredAuxiliaryCoverPreparation

/-! Measured preparation in every positive VF arity for actual Gamma
forms with finite image. All level names and the finite proper cover are
constructed over the original base, with every protected restriction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem finite_image_measured_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S) (hCA : ∀ i,(C i).carrier ⊆ A.carrier)
    (hC : ∀ i,ProperInvariant S (C i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (hFinite : ω.image.carrier.Finite)
    (hLevels : ∀ u γ,IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    Nonempty (MeasuredCoordinatePreparation (G := G) A C hCA ω) := by
  letI : Fintype ω.image := hFinite.fintype
  let l := Fintype.card ω.image
  let e : Fin l ≃ ω.image := (Fintype.equivFin ω.image).symm
  have hNamed (j : Fin l) := finiteGammaPresentation_element_named hc ω.image hFinite (e j)
  let Q (j : Fin l) := namedGammaFormLevel ω (e j).val (hNamed j)
  have hQA (j : Fin l) : (Q j).carrier ⊆ A.carrier := namedGammaFormLevel_subset ω (e j).val (hNamed j)
  have hQ (j : Fin l) : ProperInvariant S (Q j).carrier := namedGammaFormLevel_proper
    h00 hc linear hκ hs hv hsmall hΓ hA ω hLevels (e j).val (hNamed j)
  have hCover : ∀ p ∈ A.carrier,∃ j,p ∈ (Q j).carrier := by
    intro p hp
    let γ : ω.image := ⟨(ω ⟨p,hp⟩).val,⟨⟨p,hp⟩,rfl⟩⟩
    refine ⟨e.symm γ,hp,?_⟩
    change gammaFormExtension ω p=(e (e.symm γ)).val
    rw [e.apply_symm_apply]
    exact gammaFormExtension_at ω ⟨p,hp⟩
  have hConst (j : Fin l) (p q : Q j) (he : p.val.2=q.val.2) :
      ω ⟨p.val,hQA j p.property⟩=ω ⟨q.val,hQA j q.property⟩ := by
    have hp : (ω ⟨p.val,hQA j p.property⟩).val=(e j).val :=
      (gammaFormExtension_at ω ⟨p.val,hQA j p.property⟩).symm.trans p.property.2
    have hq : (ω ⟨q.val,hQA j q.property⟩).val=(e j).val :=
      (gammaFormExtension_at ω ⟨q.val,hQA j q.property⟩).symm.trans q.property.2
    exact Subtype.ext (hp.trans hq.symm)
  exact measured_preparation_of_label_constant_cover h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    A hA hAD hARV C hCA hC Q hQA hQ hCover ω hConst

end DiamondIntegral.Section6
