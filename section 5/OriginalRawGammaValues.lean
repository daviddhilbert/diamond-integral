import «section 5».OriginalRawGammaFamilies
import «section 5».NativeRawGammaFubini
import «section 5».OriginalEulerRowValues

/-! A whole original Euler certificate evaluates the complete family of
RV representatives over any raw RV base, including zero coordinates. -/
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

theorem native_raw_gamma_fubini_constant
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (c : ℤ) (hcst : ∀ x : X, rawRVGammaFibreEulerValue h00 hκ hs hr hγ T x.val kind = c) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (rawRVGammaLift h00 X T) =
      nativeTorusClass B ^ n * (c : RESDimensionFreeReduction.Ring B) *
        nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X := by
  have he := native_raw_relative_gamma_fubini h00 linear hκ hs hr hγ hΓ kind X T
  have hw := nativeRawWeightedValue_partition h00 linear hκ hs hr hγ hΓ kind X
    (fun x => rawRVGammaFibreEulerValue h00 hκ hs hr hγ T x kind)
    (raw_rv_gamma_fibre_euler_constructible h00 hκ hs hr hγ X T kind).1
    (raw_rv_gamma_fibre_euler_constructible h00 hκ hs hr hγ X T kind).2
    (fun _ : Unit => X) (fun _ : Unit => c) (fun _ => Set.Subset.rfl)
    (fun i j h => (h (Subsingleton.elim i j)).elim)
    (fun _ => ⟨fun h => ⟨(),h⟩,fun ⟨_,h⟩ => h⟩) (fun _ x => hcst x)
  simp only [Finset.univ_unique,Finset.sum_singleton] at hw
  exact (he.trans (congrArg (fun w => nativeTorusClass B ^ n * w) hw)).trans (mul_assoc _ _ _).symm

theorem originalRawGammaFamily_euler
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p n (fun _ => .rv))
    (hD : ∀ x : X, originalGammaSourceValid hc D (rvValues x.val)) (x : X) (kind : EulerKind) :
    rawRVGammaFibreEulerValue h00 hκ hs hr hγ (originalRawGammaFamily X D hD) x.val kind =
      originalGammaRowEulerValue hc h00 hκ hs hr hγ D (rvValues x.val) kind := by
  unfold originalGammaRowEulerValue
  rw [dif_pos (hD x)]
  unfold rawRVGammaFibreEulerValue
  apply GammaIntegralCongruence.integrateAll_congr
  intro γ
  dsimp only [GammaIndicators.indicatorFamily]
  have hm : (γ ∈ {γ | (x.val,γ) ∈ (originalRawGammaFamily X D hD).carrier}) ↔
      γ ∈ originalGammaSourceRow hc D (rvValues x.val) := by
    change (_ ∧ _) ↔ _
    exact and_iff_right x.property
  exact if_congr hm rfl rfl

theorem OriginalEulerCertificate.source_valid
    (C : OriginalEulerCertificate B (fun _ : Fin p => .rv) n)
    (D : GammaDomainFormula B p n (fun _ => .rv)) (z : Fin p → M) (hv : C.ValidFor hc D z) :
    originalGammaSourceValid hc D z :=
  (C.syntax hc).source_quotient_validity (nativeGammaRelationSyntax hc).proper
    (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less _ _ hv

theorem original_raw_gamma_certificate_fubini
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p n (fun _ => .rv))
    (C : OriginalEulerCertificate B (fun _ : Fin p => .rv) n)
    (hv : ∀ x : X, C.ValidFor hc D (rvValues x.val)) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
      (rawRVGammaLift h00 X (originalRawGammaFamily X D (fun x => C.source_valid D _ (hv x)))) =
      nativeTorusClass B ^ n * ((C.syntax hc).eulerValue kind : RESDimensionFreeReduction.Ring B) *
        nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X := by
  apply native_raw_gamma_fubini_constant h00 linear hκ hs hr hγ hΓ kind
  intro x
  exact (originalRawGammaFamily_euler h00 hκ hs hr hγ X D _ x kind).trans
    (C.originalGammaRowEulerValue hc h00 hκ hs hr hγ D _ (hv x) kind)

end DiamondIntegral.Section5
