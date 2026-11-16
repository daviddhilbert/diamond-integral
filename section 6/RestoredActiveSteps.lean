import «section 6».UnitBaseMapComposition

/-! Perform an active centripetal step and restore its entire base
afterwards. The restoration is ported through the actual new base
refinement, with all newly created RV labels retained. -/

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

def restoreActive
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (R : RetainedUnitBaseMap (G := G) A) (k : Fin r)
    (D : CentripetalData (G := G) (rvCoordinateBundle A k)) (hCoord : D.coordinate=Fin.last n) :
    RetainedUnitBaseMap (G := G) (rvCoordinateBundle A k) := by
  let Y := activeBundleCarriedFrame h00 hc hκ hs hv D hCoord
  let F := ofActiveStep h00 hc linear hκ hs hv hsmall hΓ k D hCoord
  let Q := (R.refine h00 hc linear hκ hs hv hsmall hΓ Y.asRVFrame).carry
    h00 hc linear hκ hs hv hsmall hΓ Y.freeLabel
  exact F.comp h00 hc linear hκ hs hv hsmall hΓ Q

theorem restoreActive_base_value
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (R : RetainedUnitBaseMap (G := G) A) (k : Fin r)
    (D : CentripetalData (G := G) (rvCoordinateBundle A k)) (hCoord : D.coordinate=Fin.last n)
    (p : rvCoordinateBundle A k) :
    Fin.init ((R.restoreActive h00 hc linear hκ hs hv hsmall hΓ k D hCoord).map p).val.1=
      (R.map (bundleProjection A k p)).val.1 := by
  let Y := activeBundleCarriedFrame h00 hc hκ hs hv D hCoord
  let R' := R.refine h00 hc linear hκ hs hv hsmall hΓ Y.asRVFrame
  change Fin.init ((R'.carry h00 hc linear hκ hs hv hsmall hΓ Y.freeLabel).map
    (activeBundleStepRetarget h00 hc hκ hs hv D hCoord p)).val.1=_
  rw [carry_base_value]
  change (R.map (Y.oldMap (activeBundleStepRetarget h00 hc hκ hs hv D hCoord p))).val.1=_
  rw [activeBundleStepRetarget_commutes]

theorem restoreActive_active_value
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (R : RetainedUnitBaseMap (G := G) A) (k : Fin r)
    (D : CentripetalData (G := G) (rvCoordinateBundle A k)) (hCoord : D.coordinate=Fin.last n)
    (p : rvCoordinateBundle A k) :
    ((R.restoreActive h00 hc linear hκ hs hv hsmall hΓ k D hCoord).map p).val.1 (Fin.last n)=
      (centripetalStepMap D p).val.1 (Fin.last n) := by
  let Y := activeBundleCarriedFrame h00 hc hκ hs hv D hCoord
  let R' := R.refine h00 hc linear hκ hs hv hsmall hΓ Y.asRVFrame
  change ((R'.carry h00 hc linear hκ hs hv hsmall hΓ Y.freeLabel).map
    (activeBundleStepRetarget h00 hc hκ hs hv D hCoord p)).val.1 (Fin.last n)=_
  rw [carry_fixed,activeBundleStepRetarget_value]

end DiamondIntegral.Section6.RetainedUnitBaseMap
