import «section 6».RetainedUnitBaseMaps

/-! A retained base restoration survives every full RV refinement.
The actual ported map retains all refining labels and its complete
base-value square, so restoration does not require a constant offset. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.RetainedUnitBaseMap
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def refine
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (R : RetainedUnitBaseMap (G := G) A) (X : RVRefinementFrame A) :
    RetainedUnitBaseMap (G := G) X.base := by
  have hT := R.home.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ R.home.bijective.surjective
  let Y := X.portTarget h00 hc hκ hs hv R.map R.home.bijective R.labels R.retained hT R.targetBounded
  exact {
    arity := Y.arity
    target := Y.base
    map := X.portMap hc R.map
    sourceBounded := X.doublyBounded
    targetBounded := Y.doublyBounded
    home := X.port_homeomorphism h00 hc linear hκ hs hv hsmall hΓ R.map R.home R.labels R.retained R.targetBounded
    labels := Fin.natAdd R.arity
    labels_injective := Fin.natAdd_injective X.arity R.arity
    retained := X.port_retained hc R.map
    unit := X.port_generic_unit hc hv R.map R.unit }

theorem refine_vf_value
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (R : RetainedUnitBaseMap (G := G) A) (X : RVRefinementFrame A) (p : X.base) :
    ((R.refine h00 hc linear hκ hs hv hsmall hΓ X).map p).val.1=(R.map (X.oldPoint p)).val.1 := rfl

theorem refine_selected_value
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (R : RetainedUnitBaseMap (G := G) A) (X : RVRefinementFrame A) (p : X.base) :
    let F := R.refine h00 hc linear hκ hs hv hsmall hΓ X
    ((F.map p).val.1,(F.map p).val.2 ∘ Fin.castAdd X.arity)=(R.map (X.oldPoint p)).val :=
  retainedRVOutput_selected hc (R.map.comp X.oldMap) p

end DiamondIntegral.Section6.RetainedUnitBaseMap
