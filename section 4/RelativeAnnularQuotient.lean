import «section 4».FunctionalApertureCompatibility
import «section 4».PolynomialCoactionQuotient

/-! The actual quotient required by bounded variable apertures. Ordinary
forgetting and both existing Euler evaluations descend through the new
relative ideal, preserving the original residue restrictions. -/
set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace DiamondIntegral.Section4.RelativeAnnularQuotient
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def Ring (B : Base (M := M)) := RVBoundedRing.Ring B ⧸ FunctionalApertureCompatibility.ideal B
  deriving CommRing

def quotient (B : Base (M := M)) : RVBoundedRing.Ring B →+* Ring B :=
  Ideal.Quotient.mk (FunctionalApertureCompatibility.ideal B)

theorem ideal_coefficients (B : Base (M := M)) :
    ∀ n x, x ∈ FunctionalApertureCompatibility.ideal B →
      (RVBoundedGrading.coaction B x).coeff n ∈ FunctionalApertureCompatibility.ideal B :=
  (RVBoundedGrading.gradingCoaction B).homogeneous_ideal_coefficients _
    (FunctionalApertureCompatibility.ideal_homogeneous B)

def coaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) :=
  (RVBoundedGrading.gradingCoaction B).quotient _ (ideal_coefficients B)

def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) := (coaction B).piece n

instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (coaction B).grading

theorem quotient_mem (B : Base (M := M)) {n : ℕ} {x : RVBoundedRing.Ring B}
    (hx : x ∈ RVBoundedGrading.gradedPiece B n) : quotient B x ∈ piece B n :=
  (RVBoundedGrading.gradingCoaction B).quotient_mem _ (ideal_coefficients B) hx

def forget (B : Base (M := M)) : Ring B →+* RVOrdinaryRing.Ring B :=
  Ideal.Quotient.lift _ (RVOrdinaryMaps.boundedForget B)
    (fun _ hx => RingHom.mem_ker.mp (FunctionalApertureCompatibility.ideal_le_forget_kernel B hx))

theorem forget_quotient (B : Base (M := M)) (x : RVBoundedRing.Ring B) :
    forget B (quotient B x)=RVOrdinaryMaps.boundedForget B x := rfl

theorem quotient_injective_on_degree_zero (B : Base (M := M)) :
    Set.InjOn (quotient B) (RVBoundedGrading.gradedPiece B 0) :=
  FunctionalApertureCompatibility.quotient_injective_on_degree_zero B

variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

def evaluation (kind : EulerKind) : Ring B →+* RESOrdinaryReduction.ReducedRing B :=
  (RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ
    (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ) kind).comp (forget B)

theorem evaluation_quotient (kind : EulerKind) (x : RVBoundedRing.Ring B) :
    evaluation hc h00 linear hκ hs B hr hγ hΓ kind (quotient B x)=
      RVT001OrdinaryDescent.boundedEvaluation h00 linear hκ hs B hr hγ hΓ
        (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ) kind x := rfl

theorem evaluation_res (kind : EulerKind) (x : RESChartRing.Ring B) :
    evaluation hc h00 linear hκ hs B hr hγ hΓ kind (quotient B (RVBoundedMaps.ofRES B x))=
      RESOrdinaryReduction.forget B x :=
  RVT001OrdinaryDescent.boundedEvaluation_res h00 linear hκ hs B hr hγ hΓ
    (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ) kind x

end DiamondIntegral.Section4.RelativeAnnularQuotient
