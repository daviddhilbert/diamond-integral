import «section 3».GammaAdditiveUnaryKernel
import «section 3».GammaGroundMeasuredRVIsomorphismClasses

/-! The unary comparison has a finite additive geometric derivation.
This auxiliary congruence records original elementary steps; it does not
replace the manuscript's principal congruence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

inductive GammaNativeElementaryStep
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) :
    GammaGroundMeasuredRVKPlus hc B (n+1) → GammaGroundMeasuredRVKPlus hc B (n+1) → Prop
  | elementary (U : GammaObjectAt B Set.univ (n+1))
      (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
      (i : Fin (n+1)) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
      GammaNativeElementaryStep hκ hs h00 hr
        (gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization U ω))
        (gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization
          (gammaElementaryAt hκ hs h00 hr U i hAd)
          (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd))))

def gammaNativeGeometricCongruence
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) :
    AddCon (GammaGroundMeasuredRVKPlus hc B (n+1)) :=
  addConGen (GammaNativeElementaryStep hκ hs h00 hr)

theorem gammaNativeGeometricQuotient_elementary
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) :
    GammaNativeElementaryInvariant (hc := hc) (n := n)
      (W := (gammaNativeGeometricCongruence (hc := hc) (n := n) hκ hs h00 hr).Quotient) hκ hs h00 hr
      (gammaNativeGeometricCongruence (hc := hc) (n := n) hκ hs h00 hr).mk' := by
  intro U ω i hAd
  exact (gammaNativeGeometricCongruence hκ hs h00 hr).eq.mpr
    (AddConGen.Rel.of _ _ (.elementary U ω i hAd))

theorem gammaNativeUnaryFullMeasured_geometric_derivation
    [CharZero (Section2.VF M)]
    {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (FBase : VFFieldBase B.real)
    (U V : GammaObjectAt B Set.univ 1)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η)) :
    AddConGen.Rel (GammaNativeElementaryStep hκ.le hs h00 hr)
      (gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization U ω))
      (gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization V η)) := by
  have H := gammaNativeUnaryFullMeasured_additive_comparison
      (W := (gammaNativeGeometricCongruence (hc := hc) (n := 0) hκ.le hs h00 hr).Quotient) hκ hs h00 hr
      (gammaNativeGeometricCongruence (hc := hc) (n := 0) hκ.le hs h00 hr).mk'
      (gammaNativeGeometricQuotient_elementary hκ.le hs h00 hr)
      hv δ hδ hδ1 FBase U V ω η f
  exact (gammaNativeGeometricCongruence hκ.le hs h00 hr).eq.mp H

end DiamondIntegral.Section3
