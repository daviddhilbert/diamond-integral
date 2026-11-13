import «section 4».IntrinsicPresentationMaps

/-! Every transported sharp and inclusion map preserves the full grading
of the intrinsic finite-union/disjoint-union presentations. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.IntrinsicPresentationGradings
open IntrinsicPresentationMaps RingPresentationTransport
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem gammaFull_inverse_mem (B : Base (M := M)) {n : ℕ} {x : GammaRVChartPresentation.ChartRing B}
    (hx : x ∈ GammaRVGrading.gradedPiece B n) : (GammaRVFiniteUnionPresentation.equivalence B).symm x ∈ GammaRVFiniteUnionGrading.piece B n := by
  have hi := inverse_eq (GammaRVFiniteUnionPresentation.equivalence B) (GammaRVFiniteUnionPresentation.fromChartRing B) (GammaRVFiniteUnionPresentation.to_from B)
  change (GammaRVFiniteUnionPresentation.equivalence B).symm.toRingHom x ∈ GammaRVFiniteUnionGrading.piece B n
  rw [hi]
  exact GammaRVFiniteUnionGrading.fromChart_mem B hx

theorem gammaBounded_inverse_mem (B : Base (M := M)) {n : ℕ} {x : GammaBoundedRVPresentation.ChartRing B}
    (hx : x ∈ GammaBoundedRVGrading.gradedPiece B n) : (GammaBoundedRVFiniteUnionPresentation.equivalence B).symm x ∈ GammaBoundedRVFiniteUnionGrading.piece B n := by
  have hi := inverse_eq (GammaBoundedRVFiniteUnionPresentation.equivalence B) (GammaBoundedRVFiniteUnionPresentation.fromChartRing B) (GammaBoundedRVFiniteUnionPresentation.to_from B)
  change (GammaBoundedRVFiniteUnionPresentation.equivalence B).symm.toRingHom x ∈ GammaBoundedRVFiniteUnionGrading.piece B n
  rw [hi]
  exact GammaBoundedRVFiniteUnionGrading.fromChart_mem B hx

theorem gammaFinite_inverse_mem (B : Base (M := M)) {n : ℕ} {x : GammaFiniteRVPresentation.ChartRing B}
    (hx : x ∈ GammaFiniteRVGrading.gradedPiece B n) : (GammaFiniteRVFiniteUnionPresentation.equivalence B).symm x ∈ GammaFiniteRVFiniteUnionGrading.piece B n := by
  have hi := inverse_eq (GammaFiniteRVFiniteUnionPresentation.equivalence B) (GammaFiniteRVFiniteUnionPresentation.fromChartRing B) (GammaFiniteRVFiniteUnionPresentation.to_from B)
  change (GammaFiniteRVFiniteUnionPresentation.equivalence B).symm.toRingHom x ∈ GammaFiniteRVFiniteUnionGrading.piece B n
  rw [hi]
  exact GammaFiniteRVFiniteUnionGrading.fromChart_mem B hx

theorem rvFull_inverse_mem (B : Base (M := M)) {n : ℕ} {x : RVChartRing.Ring B}
    (hx : x ∈ RVGrading.gradedPiece B n) : (RVDisjointPresentation.equivalence B).symm x ∈ RVDisjointGrading.piece B n := by
  have hi := inverse_eq (RVDisjointPresentation.equivalence B) (RVDisjointPresentation.fromChartRing B) (RVDisjointPresentation.to_from B)
  change (RVDisjointPresentation.equivalence B).symm.toRingHom x ∈ RVDisjointGrading.piece B n
  rw [hi]
  exact RVDisjointGrading.fromChart_mem B hx

theorem rvBounded_inverse_mem (B : Base (M := M)) {n : ℕ} {x : RVBoundedRing.Ring B}
    (hx : x ∈ RVBoundedGrading.gradedPiece B n) : (RVBoundedDisjointPresentation.equivalence B).symm x ∈ RVBoundedDisjointGrading.piece B n := by
  have hi := inverse_eq (RVBoundedDisjointPresentation.equivalence B) (RVBoundedDisjointPresentation.fromChartRing B) (RVBoundedDisjointPresentation.to_from B)
  change (RVBoundedDisjointPresentation.equivalence B).symm.toRingHom x ∈ RVBoundedDisjointGrading.piece B n
  rw [hi]
  exact RVBoundedDisjointGrading.fromChart_mem B hx

theorem res_inverse_mem (B : Base (M := M)) {n : ℕ} {x : RESChartRing.Ring B}
    (hx : x ∈ RESRingCoaction.gradedPiece B n) : (RESDisjointPresentation.equivalence B).symm x ∈ RESDisjointGrading.piece B n := by
  have hi := inverse_eq (RESDisjointPresentation.equivalence B) (RESDisjointPresentation.fromChartRing B) (RESDisjointPresentation.to_from B)
  change (RESDisjointPresentation.equivalence B).symm.toRingHom x ∈ RESDisjointGrading.piece B n
  rw [hi]
  exact RESDisjointGrading.fromChart_mem B hx

theorem gammaBoundedToFull_mem (B : Base (M := M)) {n : ℕ} {x : GammaBoundedRVFiniteUnionPresentation.Ring B}
    (hx : x ∈ GammaBoundedRVFiniteUnionGrading.piece B n) : gammaBoundedToFull B x ∈ GammaRVFiniteUnionGrading.piece B n :=
  RingPresentationTransport.map_mem (aPiece := GammaBoundedRVFiniteUnionGrading.piece B) (bPiece := GammaRVFiniteUnionGrading.piece B)
    (oldAPiece := GammaBoundedRVGrading.gradedPiece B) (oldBPiece := GammaRVGrading.gradedPiece B) (n := n)
    (GammaBoundedRVFiniteUnionPresentation.equivalence B) (GammaRVFiniteUnionPresentation.equivalence B) (GammaBoundedRVMaps.forget B)
    (fun _ _ hy => GammaBoundedRVFiniteUnionGrading.toChart_mem B hy)
    (fun _ _ hy => gammaFull_inverse_mem B hy) (fun _ _ hy => (GammaBoundedRVProfiles.gradedForget B).map_mem hy) hx

def graded_gammaBoundedToFull (B : Base (M := M)) : GradedRingHom (GammaBoundedRVFiniteUnionGrading.piece B) (GammaRVFiniteUnionGrading.piece B) where
  toRingHom := gammaBoundedToFull B
  map_mem := fun hx => gammaBoundedToFull_mem B hx

theorem gammaFiniteToFull_mem (B : Base (M := M)) {n : ℕ} {x : GammaFiniteRVFiniteUnionPresentation.Ring B}
    (hx : x ∈ GammaFiniteRVFiniteUnionGrading.piece B n) : gammaFiniteToFull B x ∈ GammaRVFiniteUnionGrading.piece B n :=
  RingPresentationTransport.map_mem (aPiece := GammaFiniteRVFiniteUnionGrading.piece B) (bPiece := GammaRVFiniteUnionGrading.piece B)
    (oldAPiece := GammaFiniteRVGrading.gradedPiece B) (oldBPiece := GammaRVGrading.gradedPiece B) (n := n)
    (GammaFiniteRVFiniteUnionPresentation.equivalence B) (GammaRVFiniteUnionPresentation.equivalence B) (GammaFiniteRVMaps.forget B)
    (fun _ _ hy => GammaFiniteRVFiniteUnionGrading.toChart_mem B hy)
    (fun _ _ hy => gammaFull_inverse_mem B hy) (fun _ _ hy => (GammaFiniteRVMapGradings.gradedForget B).map_mem hy) hx

def graded_gammaFiniteToFull (B : Base (M := M)) : GradedRingHom (GammaFiniteRVFiniteUnionGrading.piece B) (GammaRVFiniteUnionGrading.piece B) where
  toRingHom := gammaFiniteToFull B
  map_mem := fun hx => gammaFiniteToFull_mem B hx

theorem gammaFiniteToBounded_mem (B : Base (M := M)) {n : ℕ} {x : GammaFiniteRVFiniteUnionPresentation.Ring B}
    (hx : x ∈ GammaFiniteRVFiniteUnionGrading.piece B n) : gammaFiniteToBounded B x ∈ GammaBoundedRVFiniteUnionGrading.piece B n :=
  RingPresentationTransport.map_mem (aPiece := GammaFiniteRVFiniteUnionGrading.piece B) (bPiece := GammaBoundedRVFiniteUnionGrading.piece B)
    (oldAPiece := GammaFiniteRVGrading.gradedPiece B) (oldBPiece := GammaBoundedRVGrading.gradedPiece B) (n := n)
    (GammaFiniteRVFiniteUnionPresentation.equivalence B) (GammaBoundedRVFiniteUnionPresentation.equivalence B) (GammaFiniteRVMaps.bounded B)
    (fun _ _ hy => GammaFiniteRVFiniteUnionGrading.toChart_mem B hy)
    (fun _ _ hy => gammaBounded_inverse_mem B hy) (fun _ _ hy => (GammaFiniteRVMapGradings.gradedBounded B).map_mem hy) hx

def graded_gammaFiniteToBounded (B : Base (M := M)) : GradedRingHom (GammaFiniteRVFiniteUnionGrading.piece B) (GammaBoundedRVFiniteUnionGrading.piece B) where
  toRingHom := gammaFiniteToBounded B
  map_mem := fun hx => gammaFiniteToBounded_mem B hx

theorem fullSharp_mem (B : Base (M := M)) {n : ℕ} {x : GammaRVFiniteUnionPresentation.Ring B}
    (hx : x ∈ GammaRVFiniteUnionGrading.piece B n) : fullSharp B x ∈ RVDisjointGrading.piece B n :=
  RingPresentationTransport.map_mem (aPiece := GammaRVFiniteUnionGrading.piece B) (bPiece := RVDisjointGrading.piece B)
    (oldAPiece := GammaRVGrading.gradedPiece B) (oldBPiece := RVGrading.gradedPiece B) (n := n)
    (GammaRVFiniteUnionPresentation.equivalence B) (RVDisjointPresentation.equivalence B) (RVSharpRingMap.sharp B)
    (fun _ _ hy => GammaRVFiniteUnionGrading.toChart_mem B hy)
    (fun _ _ hy => rvFull_inverse_mem B hy) (fun _ _ hy => (GammaRVMapGradings.gradedSharp B).map_mem hy) hx

def graded_fullSharp (B : Base (M := M)) : GradedRingHom (GammaRVFiniteUnionGrading.piece B) (RVDisjointGrading.piece B) where
  toRingHom := fullSharp B
  map_mem := fun hx => fullSharp_mem B hx

theorem boundedSharp_mem (B : Base (M := M)) {n : ℕ} {x : GammaBoundedRVFiniteUnionPresentation.Ring B}
    (hx : x ∈ GammaBoundedRVFiniteUnionGrading.piece B n) : boundedSharp B x ∈ RVBoundedDisjointGrading.piece B n :=
  RingPresentationTransport.map_mem (aPiece := GammaBoundedRVFiniteUnionGrading.piece B) (bPiece := RVBoundedDisjointGrading.piece B)
    (oldAPiece := GammaBoundedRVGrading.gradedPiece B) (oldBPiece := RVBoundedGrading.gradedPiece B) (n := n)
    (GammaBoundedRVFiniteUnionPresentation.equivalence B) (RVBoundedDisjointPresentation.equivalence B) (GammaBoundedRVMaps.sharp B)
    (fun _ _ hy => GammaBoundedRVFiniteUnionGrading.toChart_mem B hy)
    (fun _ _ hy => rvBounded_inverse_mem B hy) (fun _ _ hy => (GammaBoundedRVProfiles.gradedSharp B).map_mem hy) hx

def graded_boundedSharp (B : Base (M := M)) : GradedRingHom (GammaBoundedRVFiniteUnionGrading.piece B) (RVBoundedDisjointGrading.piece B) where
  toRingHom := boundedSharp B
  map_mem := fun hx => boundedSharp_mem B hx

theorem finiteSharp_mem (B : Base (M := M)) {n : ℕ} {x : GammaFiniteRVFiniteUnionPresentation.Ring B}
    (hx : x ∈ GammaFiniteRVFiniteUnionGrading.piece B n) : finiteSharp B x ∈ RESDisjointGrading.piece B n :=
  RingPresentationTransport.map_mem (aPiece := GammaFiniteRVFiniteUnionGrading.piece B) (bPiece := RESDisjointGrading.piece B)
    (oldAPiece := GammaFiniteRVGrading.gradedPiece B) (oldBPiece := RESRingCoaction.gradedPiece B) (n := n)
    (GammaFiniteRVFiniteUnionPresentation.equivalence B) (RESDisjointPresentation.equivalence B) (GammaFiniteRVMaps.sharp B)
    (fun _ _ hy => GammaFiniteRVFiniteUnionGrading.toChart_mem B hy)
    (fun _ _ hy => res_inverse_mem B hy) (fun _ _ hy => (GammaFiniteRVMapGradings.gradedSharp B).map_mem hy) hx

def graded_finiteSharp (B : Base (M := M)) : GradedRingHom (GammaFiniteRVFiniteUnionGrading.piece B) (RESDisjointGrading.piece B) where
  toRingHom := finiteSharp B
  map_mem := fun hx => finiteSharp_mem B hx

theorem resToFull_mem (B : Base (M := M)) {n : ℕ} {x : RESDisjointPresentation.Ring B}
    (hx : x ∈ RESDisjointGrading.piece B n) : resToFull B x ∈ RVDisjointGrading.piece B n :=
  RingPresentationTransport.map_mem (aPiece := RESDisjointGrading.piece B) (bPiece := RVDisjointGrading.piece B)
    (oldAPiece := RESRingCoaction.gradedPiece B) (oldBPiece := RVGrading.gradedPiece B) (n := n)
    (RESDisjointPresentation.equivalence B) (RVDisjointPresentation.equivalence B) (RVChartMaps.ofRES B)
    (fun _ _ hy => RESDisjointGrading.toChart_mem B hy)
    (fun _ _ hy => rvFull_inverse_mem B hy) (fun _ _ hy => RVChartMaps.ofRES_mem B hy) hx

def graded_resToFull (B : Base (M := M)) : GradedRingHom (RESDisjointGrading.piece B) (RVDisjointGrading.piece B) where
  toRingHom := resToFull B
  map_mem := fun hx => resToFull_mem B hx

theorem resToBounded_mem (B : Base (M := M)) {n : ℕ} {x : RESDisjointPresentation.Ring B}
    (hx : x ∈ RESDisjointGrading.piece B n) : resToBounded B x ∈ RVBoundedDisjointGrading.piece B n :=
  RingPresentationTransport.map_mem (aPiece := RESDisjointGrading.piece B) (bPiece := RVBoundedDisjointGrading.piece B)
    (oldAPiece := RESRingCoaction.gradedPiece B) (oldBPiece := RVBoundedGrading.gradedPiece B) (n := n)
    (RESDisjointPresentation.equivalence B) (RVBoundedDisjointPresentation.equivalence B) (RVBoundedMaps.ofRES B)
    (fun _ _ hy => RESDisjointGrading.toChart_mem B hy)
    (fun _ _ hy => rvBounded_inverse_mem B hy) (fun _ _ hy => RVBoundedMaps.ofRES_mem B hy) hx

def graded_resToBounded (B : Base (M := M)) : GradedRingHom (RESDisjointGrading.piece B) (RVBoundedDisjointGrading.piece B) where
  toRingHom := resToBounded B
  map_mem := fun hx => resToBounded_mem B hx

theorem rvBoundedToFull_mem (B : Base (M := M)) {n : ℕ} {x : RVBoundedDisjointPresentation.Ring B}
    (hx : x ∈ RVBoundedDisjointGrading.piece B n) : rvBoundedToFull B x ∈ RVDisjointGrading.piece B n :=
  RingPresentationTransport.map_mem (aPiece := RVBoundedDisjointGrading.piece B) (bPiece := RVDisjointGrading.piece B)
    (oldAPiece := RVBoundedGrading.gradedPiece B) (oldBPiece := RVGrading.gradedPiece B) (n := n)
    (RVBoundedDisjointPresentation.equivalence B) (RVDisjointPresentation.equivalence B) (RVBoundedMaps.forget B)
    (fun _ _ hy => RVBoundedDisjointGrading.toChart_mem B hy)
    (fun _ _ hy => rvFull_inverse_mem B hy) (fun _ _ hy => RVBoundedMaps.forget_mem B hy) hx

def graded_rvBoundedToFull (B : Base (M := M)) : GradedRingHom (RVBoundedDisjointGrading.piece B) (RVDisjointGrading.piece B) where
  toRingHom := rvBoundedToFull B
  map_mem := fun hx => rvBoundedToFull_mem B hx

end DiamondIntegral.Section4.IntrinsicPresentationGradings
