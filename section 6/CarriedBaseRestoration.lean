import «section 6».RefinedBaseRestoration
import «section 6».CarriedUnaryHomeChains

/-! An arbitrary retained base restoration carries a whole labelled VF
disc without changing its VF point. Bounds, actual proper covariance,
all old labels and generic unit total derivatives are retained. -/

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

def carry
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (R : RetainedUnitBaseMap (G := G) A) (k : Fin r) :
    RetainedUnitBaseMap (G := G) (rvCoordinateBundle A k) := by
  have hA := R.home.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ
  have hB := R.home.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ R.home.bijective.surjective
  exact {
    arity := R.arity
    target := rvCoordinateBundle R.target (R.labels k)
    map := carryLastMap R.map k (R.labels k) (fun p => R.retained p k)
    sourceBounded := rvCoordinateBundle_doublyBounded A k R.sourceBounded hA.rvBounded
    targetBounded := rvCoordinateBundle_doublyBounded R.target (R.labels k) R.targetBounded hB.rvBounded
    home := carryLastMap_properHomeomorphism R.map k (R.labels k) (fun p => R.retained p k)
      h00 hc linear hκ hs hv hsmall hΓ R.home
    labels := R.labels
    labels_injective := R.labels_injective
    retained := carryLastMap_retains_labels R.map k (R.labels k) (fun p => R.retained p k) R.labels R.retained
    unit := fun p hInd => carryLastMap_unit_derivative h00 hc hκ hs hv R.map hA k (R.labels k)
      (fun p => R.retained p k) p
      (R.unit (bundleProjection A k p) (hInd.comp Fin.castSucc (Fin.castSucc_injective n))) }

theorem carry_fixed
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (R : RetainedUnitBaseMap (G := G) A) (k : Fin r) (p : rvCoordinateBundle A k) :
    ((R.carry h00 hc linear hκ hs hv hsmall hΓ k).map p).val.1 (Fin.last n)=p.val.1 (Fin.last n) :=
  carryLastMap_fixed R.map k (R.labels k) (fun p => R.retained p k) p

theorem carry_base_value
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (R : RetainedUnitBaseMap (G := G) A) (k : Fin r) (p : rvCoordinateBundle A k) :
    Fin.init ((R.carry h00 hc linear hκ hs hv hsmall hΓ k).map p).val.1=
      (R.map (bundleProjection A k p)).val.1 := by
  change Fin.init (carryLastMap R.map k (R.labels k) (fun p => R.retained p k) p).val.1=_
  rw [carryLastMap_value,Fin.init_snoc]

end DiamondIntegral.Section6.RetainedUnitBaseMap
