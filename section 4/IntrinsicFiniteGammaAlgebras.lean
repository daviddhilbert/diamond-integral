import «section 4».IntrinsicPresentationMaps
import «section 4».FiniteGammaAlgebras

/-! Finite-Gamma algebra structures on the intrinsic presentations.
The coefficient ring is the existing intrinsic finite-Gamma ring,
explicitly identified with its finite-union presentation. All algebra
structures are transported along proved equivalences. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.IntrinsicFiniteGammaAlgebras
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Coeff (B : Base (M := M)) := GammaFiniteRVPresentation.ChartRing B

instance resAlgebra (B : Base (M := M)) : Algebra (Coeff B) (RESDisjointPresentation.Ring B) :=
  ((RESDisjointPresentation.equivalence B).symm.toRingHom.comp (GammaFiniteRVMaps.sharp B)).toAlgebra
instance gammaAlgebra (B : Base (M := M)) : Algebra (Coeff B) (GammaRVFiniteUnionPresentation.Ring B) :=
  ((GammaRVFiniteUnionPresentation.equivalence B).symm.toRingHom.comp (GammaFiniteRVMaps.forget B)).toAlgebra
instance boundedGammaAlgebra (B : Base (M := M)) : Algebra (Coeff B) (GammaBoundedRVFiniteUnionPresentation.Ring B) :=
  ((GammaBoundedRVFiniteUnionPresentation.equivalence B).symm.toRingHom.comp (GammaFiniteRVMaps.bounded B)).toAlgebra
instance rvAlgebra (B : Base (M := M)) : Algebra (Coeff B) (RVDisjointPresentation.Ring B) :=
  ((RVDisjointPresentation.equivalence B).symm.toRingHom.comp ((RVChartMaps.ofRES B).comp (GammaFiniteRVMaps.sharp B))).toAlgebra
instance boundedRVAlgebra (B : Base (M := M)) : Algebra (Coeff B) (RVBoundedDisjointPresentation.Ring B) :=
  ((RVBoundedDisjointPresentation.equivalence B).symm.toRingHom.comp ((RVBoundedMaps.ofRES B).comp (GammaFiniteRVMaps.sharp B))).toAlgebra

def resEquivalence (B : Base (M := M)) : RESDisjointPresentation.Ring B ≃ₐ[Coeff B] RESChartRing.Ring B where
  __ := RESDisjointPresentation.equivalence B
  commutes' c := (RESDisjointPresentation.equivalence B).apply_symm_apply (GammaFiniteRVMaps.sharp B c)

def gammaEquivalence (B : Base (M := M)) : GammaRVFiniteUnionPresentation.Ring B ≃ₐ[Coeff B] GammaRVChartPresentation.ChartRing B where
  __ := GammaRVFiniteUnionPresentation.equivalence B
  commutes' c := (GammaRVFiniteUnionPresentation.equivalence B).apply_symm_apply (GammaFiniteRVMaps.forget B c)

def boundedGammaEquivalence (B : Base (M := M)) : GammaBoundedRVFiniteUnionPresentation.Ring B ≃ₐ[Coeff B] GammaBoundedRVPresentation.ChartRing B where
  __ := GammaBoundedRVFiniteUnionPresentation.equivalence B
  commutes' c := (GammaBoundedRVFiniteUnionPresentation.equivalence B).apply_symm_apply (GammaFiniteRVMaps.bounded B c)

def rvEquivalence (B : Base (M := M)) : RVDisjointPresentation.Ring B ≃ₐ[Coeff B] RVChartRing.Ring B where
  __ := RVDisjointPresentation.equivalence B
  commutes' c := (RVDisjointPresentation.equivalence B).apply_symm_apply (RVChartMaps.ofRES B (GammaFiniteRVMaps.sharp B c))

def boundedRVEquivalence (B : Base (M := M)) : RVBoundedDisjointPresentation.Ring B ≃ₐ[Coeff B] RVBoundedRing.Ring B where
  __ := RVBoundedDisjointPresentation.equivalence B
  commutes' c := (RVBoundedDisjointPresentation.equivalence B).apply_symm_apply (RVBoundedMaps.ofRES B (GammaFiniteRVMaps.sharp B c))

theorem coefficient_res (B : Base (M := M)) :
    algebraMap (Coeff B) (RESDisjointPresentation.Ring B) =
      (IntrinsicPresentationMaps.finiteSharp B).comp (GammaFiniteRVFiniteUnionPresentation.equivalence B).symm.toRingHom := by
  ext c
  change (RESDisjointPresentation.equivalence B).symm (GammaFiniteRVMaps.sharp B c) =
    (RESDisjointPresentation.equivalence B).symm (GammaFiniteRVMaps.sharp B
      ((GammaFiniteRVFiniteUnionPresentation.equivalence B) ((GammaFiniteRVFiniteUnionPresentation.equivalence B).symm c)))
  rw [RingEquiv.apply_symm_apply]

theorem coefficient_gamma (B : Base (M := M)) :
    algebraMap (Coeff B) (GammaRVFiniteUnionPresentation.Ring B) =
      (IntrinsicPresentationMaps.gammaFiniteToFull B).comp (GammaFiniteRVFiniteUnionPresentation.equivalence B).symm.toRingHom := by
  ext c
  change (GammaRVFiniteUnionPresentation.equivalence B).symm (GammaFiniteRVMaps.forget B c) =
    (GammaRVFiniteUnionPresentation.equivalence B).symm (GammaFiniteRVMaps.forget B
      ((GammaFiniteRVFiniteUnionPresentation.equivalence B) ((GammaFiniteRVFiniteUnionPresentation.equivalence B).symm c)))
  rw [RingEquiv.apply_symm_apply]

theorem coefficient_boundedGamma (B : Base (M := M)) :
    algebraMap (Coeff B) (GammaBoundedRVFiniteUnionPresentation.Ring B) =
      (IntrinsicPresentationMaps.gammaFiniteToBounded B).comp (GammaFiniteRVFiniteUnionPresentation.equivalence B).symm.toRingHom := by
  ext c
  change (GammaBoundedRVFiniteUnionPresentation.equivalence B).symm (GammaFiniteRVMaps.bounded B c) =
    (GammaBoundedRVFiniteUnionPresentation.equivalence B).symm (GammaFiniteRVMaps.bounded B
      ((GammaFiniteRVFiniteUnionPresentation.equivalence B) ((GammaFiniteRVFiniteUnionPresentation.equivalence B).symm c)))
  rw [RingEquiv.apply_symm_apply]

end DiamondIntegral.Section4.IntrinsicFiniteGammaAlgebras
