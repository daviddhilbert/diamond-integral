import «section 5».OriginalRawGammaTotalLifts
import «section 5».OriginalRawGammaValues

/-! Whole original Euler certificates evaluate literal total RV families
over the original raw base, with no choice of representatives. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

theorem original_gamma_total_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p n (fun _ => .rv))
    (C : OriginalEulerCertificate B (fun _ : Fin p => .rv) n)
    (hv : ∀ x : X, C.ValidFor hc D (rvValues x.val)) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X D) =
      nativeTorusClass B ^ n * ((C.syntax hc).eulerValue kind : RESDimensionFreeReduction.Ring B) *
        nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X :=
  (nativeRVSetValue_raw_unit_bijection h00 linear hκ hs hr hγ hΓ kind _ _
    (originalRawGammaTotalBijection h00 X D (fun x => C.source_valid D _ (hv x)))).trans
      (original_raw_gamma_certificate_fubini h00 linear hκ hs hr hγ hΓ kind X D C hv)

end DiamondIntegral.Section5
