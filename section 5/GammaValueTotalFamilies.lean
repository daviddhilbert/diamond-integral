import «section 5».GammaValueSchemata
import «section 5».OriginalRawGammaValues
import «section 5».OriginalRawGammaTotalLifts
import «section 4».GammaPointFamilies

/-! A varying Gamma-value schema has a singleton actual Gamma row and
its full total RV family has one native torus factor. No RV lift of the
varying value is chosen over the original parameter base. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ}

theorem GammaValueSchema.source_valid
    (F : GammaValueSchema B p (fun _ => .rv)) (z : Fin p → M) (h : F.Valid hc z) :
    originalGammaSourceValid hc F.domain z := h.2.1

theorem GammaValueSchema.source_row_singleton
    (F : GammaValueSchema B p (fun _ => .rv)) (z : Fin p → M) (h : F.Valid hc z) :
    originalGammaSourceRow hc F.domain z = {fun _ : Fin 1 => F.value hc z h} := by
  ext γ
  obtain ⟨v,hp,hv⟩ := gamma_tuple_code_surjective γ
  have hr := originalGammaSourceRow_represents hc F.domain z (F.source_valid z h) v
  rw [hv] at hr
  have hraw : Fin.append z v ∈ F.domain.val ↔ γ ∈ originalGammaSourceRow hc F.domain z :=
    (gammaDomainSyntax_realize hc B F.domain z v).symm.trans (hr.trans (and_iff_right hp))
  have hvalue := F.value_row hc z h v
  have he0 : codeValue (v 0) = γ 0 := congrFun hv 0
  rw [he0] at hvalue
  have he : γ ∈ originalGammaSourceRow hc F.domain z ↔ γ 0 = F.value hc z h :=
    hraw.symm.trans (hvalue.trans (and_iff_right hp))
  rw [he,Set.mem_singleton_iff]
  constructor
  · intro hg
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    exact hj ▸ hg
  · exact fun hg => congrFun hg 0

theorem GammaValueSchema.total_fibre_euler
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : GammaValueSchema B p (fun _ => .rv))
    (hF : ∀ x : X, F.Valid hc (rvValues x.val)) (x : X) (kind : EulerKind) :
    rawRVGammaFibreEulerValue h00 hκ hs hr hγ
      (originalRawGammaFamily X F.domain (fun x => F.source_valid _ (hF x))) x.val kind = 1 := by
  rw [originalRawGammaFamily_euler]
  unfold originalGammaRowEulerValue
  rw [dif_pos (F.source_valid _ (hF x))]
  apply GammaPointFamilies.integrateAll_singleton h00 hκ hs
    ⟨B.real ∪ Set.range (rvValues x.val),B.gamma⟩ _ _ kind 1 _ (fun _ => F.value hc _ (hF x)) 1
  intro γ
  dsimp only [GammaIndicators.indicatorFamily]
  have he : γ ∈ originalGammaSourceRow hc F.domain (rvValues x.val) ↔
      γ = (fun _ : Fin 1 => F.value hc _ (hF x)) :=
    (Set.ext_iff.mp (F.source_row_singleton _ (hF x)) γ).trans Set.mem_singleton_iff
  exact if_congr he rfl rfl

theorem gamma_value_total_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : GammaValueSchema B p (fun _ => .rv))
    (hF : ∀ x : X, F.Valid hc (rvValues x.val)) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X F.domain) =
      nativeTorusClass B * nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X := by
  have he := nativeRVSetValue_raw_unit_bijection h00 linear hκ hs hr hγ hΓ kind _ _
    (originalRawGammaTotalBijection h00 X F.domain (fun x => F.source_valid _ (hF x)))
  have hraw := native_raw_gamma_fubini_constant h00 linear hκ hs hr hγ hΓ kind X
    (originalRawGammaFamily X F.domain (fun x => F.source_valid _ (hF x))) 1
      (fun x => F.total_fibre_euler h00 hκ hs hr hγ X hF x kind)
  exact he.trans (by simpa only [pow_one,Int.cast_one,mul_one] using hraw)

end DiamondIntegral.Section5
