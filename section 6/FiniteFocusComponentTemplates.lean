import «section 6».PromotedFocusComponentTemplates
import Section3.SmallFiniteParameters

/-! Genuine compactness for complete permitted component templates,
including finite named metadata and every protected source test. The
uniform choice of whole finite sequences is a separate remaining step. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_focus_component_templates
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (X : Set (Fin p → M)) (hX : S.Definable LRV X)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (hLocal : ∀ a ∈ X,∃ D : CentripetalData (G := G) (A.fibre a),IsRVPullback (A.fibre a).carrier ∧
      ∃ E : ∀ i,CentripetalData (G := G) ((P i).fibre a),∀ i,ApertureRestrictionData D (E i)) :
    ∃ l : ℕ,∃ T : Fin l → FocusComponentParameterTemplate (M := M) S p n r,
      ∀ a ∈ X,∃ i,a ∈ (T i).good A P := by
  let C := Set.range (fun T : FocusComponentParameterTemplate (M := M) S p n r => T.good A P)
  have hC : ∀ c ∈ C,S.Definable LRV c := by rintro c ⟨T,rfl⟩; exact T.good_definable A P
  have hCover (a) (ha : a ∈ X) : ∃ c ∈ C,a ∈ c := by
    obtain ⟨D,hARV,E,hE⟩ := hLocal a ha
    have hsmallA := small_union_range hκ.le S hsmall a
    have hGammaA : NontrivialDefinableGamma (⟨S ∪ Set.range a,∅⟩ : ParameterBase M) :=
      hΓ.mono Set.subset_union_left (Set.Subset.rfl)
    obtain ⟨T,hT,hRest⟩ := exists_promoted_focus_component_template h00 hc linear hκ hs hv A P a hsmallA hGammaA D hARV E hE
    exact ⟨T.good A P,⟨T,rfl⟩,hT⟩
  obtain ⟨C₀,hFin,hSub,hCov⟩ := hs.definable_finite_subcover_tuple S hsmall X hX C hC hCover
  letI : Fintype C₀ := hFin.fintype
  let e := Fintype.equivFin C₀
  let chooseT (c : C₀) := (hSub c.property).choose
  have hT (c : C₀) : (chooseT c).good A P=c.val := (hSub c.property).choose_spec
  refine ⟨Fintype.card C₀,fun i => chooseT (e.symm i),?_⟩
  intro a ha
  obtain ⟨c,hc,hac⟩ := hCov a ha
  refine ⟨e ⟨c,hc⟩,?_⟩
  change a ∈ (chooseT (e.symm (e ⟨c,hc⟩))).good A P
  rw [e.symm_apply_apply,hT]
  exact hac

end DiamondIntegral.Section6
