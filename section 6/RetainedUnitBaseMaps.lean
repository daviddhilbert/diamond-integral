import «section 6».RetainedRVOutputHomeomorphisms
import «section 6».InverseUnitDerivatives

/-! Actual bounded base maps that retain all current labels. Pulling
such a map back through a new base homeomorphism constructs its inverse
on the actual new source and retains every newly created RV label. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

structure RetainedUnitBaseMap (A : DefSet (rawMixedSpace (M := M) n r) S) where
  arity : ℕ
  target : DefSet (rawMixedSpace (M := M) n arity) S
  map : Map A target
  sourceBounded : VFDoublyBounded A.carrier
  targetBounded : VFDoublyBounded target.carrier
  home : ProperCovariantHomeomorphism map
  labels : Fin r → Fin arity
  labels_injective : Function.Injective labels
  retained : ∀ p : A,∀ i,(map p).val.2 (labels i)=p.val.2 i
  unit : ∀ p : A,AlgebraicIndependent (vfParameterField S) p.val.1 → HasMixedUnitDerivativeAt map p

namespace RetainedUnitBaseMap

def identity
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) : RetainedUnitBaseMap (G := G) A where
  arity := r
  target := A
  map := Map.id A
  sourceBounded := hAD
  targetBounded := hAD
  home := identity_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ hA
  labels := id
  labels_injective := Function.injective_id
  retained := fun _ _ => rfl
  unit := fun p _ => identity_unit_derivative hA p

def pullback
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (R : RetainedUnitBaseMap (G := G) A) (g : Map A B)
    (hg : ProperCovariantHomeomorphism g) (hBD : VFDoublyBounded B.carrier)
    (hUnit : ∀ p : A,AlgebraicIndependent (vfParameterField S) p.val.1 → HasMixedUnitDerivativeAt g p) :
    RetainedUnitBaseMap (G := G) B := by
  let I := g.inverse hg.bijective
  let f := R.map.comp I
  have hI := inverse_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ g hg
  have hF : ProperCovariantHomeomorphism f := lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ hI R.home
  refine {
    arity := R.arity+s
    target := (retainedRVOutputMap hc f).image
    map := retainedRVOutput hc f
    sourceBounded := hBD
    targetBounded := retainedRVOutput_target_doublyBounded hc f R.targetBounded
    home := retainedRVOutput_homeomorphism h00 hc linear hκ hs hv hsmall hΓ f hF hBD R.targetBounded
    labels := Fin.natAdd R.arity
    labels_injective := Fin.natAdd_injective s R.arity
    retained := retainedRVOutput_retained hc f
    unit := ?_ }
  intro q hInd
  have hInv := inverse_generic_unit_derivative h00 hc hκ.le hs hsmall hv g hg.bijective hUnit q hInd
  have hIndI := independent_map_of_finiteFibres hc I (Map.finiteFibres_of_injective hI.bijective.injective) q hInd
  have hComp : HasMixedUnitDerivativeAt f q := (R.unit (I q) hIndI).comp hInv
  exact retainedRVOutput_unit_derivative hc f q hComp

theorem pullback_vf_value
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (R : RetainedUnitBaseMap (G := G) A) (g : Map A B)
    (hg : ProperCovariantHomeomorphism g) (hBD : VFDoublyBounded B.carrier)
    (hUnit : ∀ p : A,AlgebraicIndependent (vfParameterField S) p.val.1 → HasMixedUnitDerivativeAt g p)
    (q : B) :
    ((R.pullback h00 hc linear hκ hs hv hsmall hΓ g hg hBD hUnit).map q).val.1=
      (R.map (g.inverse hg.bijective q)).val.1 := rfl

theorem pullback_restores
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (R : RetainedUnitBaseMap (G := G) A) (g : Map A B)
    (hg : ProperCovariantHomeomorphism g) (hBD : VFDoublyBounded B.carrier)
    (hUnit : ∀ p : A,AlgebraicIndependent (vfParameterField S) p.val.1 → HasMixedUnitDerivativeAt g p)
    (p : A) :
    ((R.pullback h00 hc linear hκ hs hv hsmall hΓ g hg hBD hUnit).map (g p)).val.1=(R.map p).val.1 := by
  rw [pullback_vf_value,Map.inverse_apply]

end RetainedUnitBaseMap
end DiamondIntegral.Section6
