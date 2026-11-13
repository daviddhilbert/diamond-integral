import «section 4».RingPresentationTransport
import «section 4».GammaRVFiniteUnionGrading
import «section 4».GammaBoundedRVFiniteUnionGrading
import «section 4».GammaFiniteRVFiniteUnionGrading
import «section 4».GammaFiniteRVMapGradings
import «section 4».RVDisjointGrading
import «section 4».RVBoundedDisjointGrading
import «section 4».RESDisjointGrading

/-! Actual sharp and inclusion maps between the intrinsic finite-union
and disjoint-union presentations. The complete comparison squares are
transported through the proved equivalences, retaining object formulas. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.IntrinsicPresentationMaps
open RingPresentationTransport
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gammaBoundedToFull (B : Base (M := M)) : GammaBoundedRVFiniteUnionPresentation.Ring B →+* GammaRVFiniteUnionPresentation.Ring B :=
  transport (GammaBoundedRVFiniteUnionPresentation.equivalence B) (GammaRVFiniteUnionPresentation.equivalence B) (GammaBoundedRVMaps.forget B)

def gammaFiniteToFull (B : Base (M := M)) : GammaFiniteRVFiniteUnionPresentation.Ring B →+* GammaRVFiniteUnionPresentation.Ring B :=
  transport (GammaFiniteRVFiniteUnionPresentation.equivalence B) (GammaRVFiniteUnionPresentation.equivalence B) (GammaFiniteRVMaps.forget B)

def gammaFiniteToBounded (B : Base (M := M)) : GammaFiniteRVFiniteUnionPresentation.Ring B →+* GammaBoundedRVFiniteUnionPresentation.Ring B :=
  transport (GammaFiniteRVFiniteUnionPresentation.equivalence B) (GammaBoundedRVFiniteUnionPresentation.equivalence B) (GammaFiniteRVMaps.bounded B)

def fullSharp (B : Base (M := M)) : GammaRVFiniteUnionPresentation.Ring B →+* RVDisjointPresentation.Ring B :=
  transport (GammaRVFiniteUnionPresentation.equivalence B) (RVDisjointPresentation.equivalence B) (RVSharpRingMap.sharp B)

def boundedSharp (B : Base (M := M)) : GammaBoundedRVFiniteUnionPresentation.Ring B →+* RVBoundedDisjointPresentation.Ring B :=
  transport (GammaBoundedRVFiniteUnionPresentation.equivalence B) (RVBoundedDisjointPresentation.equivalence B) (GammaBoundedRVMaps.sharp B)

def finiteSharp (B : Base (M := M)) : GammaFiniteRVFiniteUnionPresentation.Ring B →+* RESDisjointPresentation.Ring B :=
  transport (GammaFiniteRVFiniteUnionPresentation.equivalence B) (RESDisjointPresentation.equivalence B) (GammaFiniteRVMaps.sharp B)

def resToFull (B : Base (M := M)) : RESDisjointPresentation.Ring B →+* RVDisjointPresentation.Ring B :=
  transport (RESDisjointPresentation.equivalence B) (RVDisjointPresentation.equivalence B) (RVChartMaps.ofRES B)

def resToBounded (B : Base (M := M)) : RESDisjointPresentation.Ring B →+* RVBoundedDisjointPresentation.Ring B :=
  transport (RESDisjointPresentation.equivalence B) (RVBoundedDisjointPresentation.equivalence B) (RVBoundedMaps.ofRES B)

def rvBoundedToFull (B : Base (M := M)) : RVBoundedDisjointPresentation.Ring B →+* RVDisjointPresentation.Ring B :=
  transport (RVBoundedDisjointPresentation.equivalence B) (RVDisjointPresentation.equivalence B) (RVBoundedMaps.forget B)

theorem gamma_forget_bounded (B : Base (M := M)) :
    (gammaBoundedToFull B).comp (gammaFiniteToBounded B) = gammaFiniteToFull B := by
  unfold gammaBoundedToFull gammaFiniteToBounded gammaFiniteToFull
  rw [transport_comp, GammaFiniteRVMaps.forget_bounded]

theorem bounded_sharp_square (B : Base (M := M)) :
    (rvBoundedToFull B).comp (boundedSharp B) = (fullSharp B).comp (gammaBoundedToFull B) := by
  unfold rvBoundedToFull boundedSharp fullSharp gammaBoundedToFull
  rw [transport_comp, transport_comp, GammaBoundedRVMaps.forget_sharp]

theorem finite_full_sharp_square (B : Base (M := M)) :
    (resToFull B).comp (finiteSharp B) = (fullSharp B).comp (gammaFiniteToFull B) := by
  unfold resToFull finiteSharp fullSharp gammaFiniteToFull
  rw [transport_comp, transport_comp, GammaFiniteRVMaps.sharp_full_comparison]

theorem finite_bounded_sharp_square (B : Base (M := M)) :
    (resToBounded B).comp (finiteSharp B) = (boundedSharp B).comp (gammaFiniteToBounded B) := by
  unfold resToBounded finiteSharp boundedSharp gammaFiniteToBounded
  rw [transport_comp, transport_comp, GammaFiniteRVMaps.sharp_bounded_comparison]

theorem fullSharp_single (B : Base (M := M)) {n : ℕ} (a : GammaWeightedCharts.Chart B n) :
    fullSharp B (GammaRVFiniteUnionPresentation.singleClass a) = RVDisjointPresentation.objectClass (RVSharpCharts.sharpChart a) := by
  apply transport_value
  change RVSharpRingMap.sharp B (GammaRVFiniteUnionPresentation.toChartRing B (GammaRVFiniteUnionPresentation.singleClass a)) =
    RVDisjointPresentation.toChartRing B (RVDisjointPresentation.objectClass (RVSharpCharts.sharpChart a))
  rw [GammaRVFiniteUnionPresentation.toChart_single, RVDisjointPresentation.toChartRing_class]
  exact RVSharpRingMap.sharp_class B a

theorem boundedSharp_single (B : Base (M := M)) {n : ℕ} (a : GammaBoundedRVCharts.BoundedChart B n) :
    boundedSharp B (GammaBoundedRVFiniteUnionPresentation.singleClass a) =
      RVBoundedDisjointPresentation.objectClass (GammaBoundedRVCharts.sharp a) := by
  apply transport_value
  change GammaBoundedRVMaps.sharp B (GammaBoundedRVFiniteUnionPresentation.toChartRing B (GammaBoundedRVFiniteUnionPresentation.singleClass a)) =
    RVBoundedDisjointPresentation.toChartRing B (RVBoundedDisjointPresentation.objectClass (GammaBoundedRVCharts.sharp a))
  rw [GammaBoundedRVFiniteUnionPresentation.toChart_single, RVBoundedDisjointPresentation.toChartRing_class]
  exact GammaBoundedRVMaps.sharp_class B a

theorem finiteSharp_single (B : Base (M := M)) {n : ℕ} (a : GammaFiniteRVCharts.FiniteChart B n) :
    finiteSharp B (GammaFiniteRVFiniteUnionPresentation.singleClass a) = RESDisjointPresentation.objectClass (GammaFiniteRVCharts.sharp a) := by
  apply transport_value
  change GammaFiniteRVMaps.sharp B (GammaFiniteRVFiniteUnionPresentation.toChartRing B (GammaFiniteRVFiniteUnionPresentation.singleClass a)) =
    RESDisjointPresentation.toChartRing B (RESDisjointPresentation.objectClass (GammaFiniteRVCharts.sharp a))
  rw [GammaFiniteRVFiniteUnionPresentation.toChart_single, RESDisjointPresentation.toChartRing_class]
  exact GammaFiniteRVMaps.sharp_class B a

end DiamondIntegral.Section4.IntrinsicPresentationMaps
