import «section 5».OriginalProductTotalBijections
import «section 5».OriginalGammaTotalValues

/-! Relative Gamma Fubini evaluates literal total product families over
the full first-factor total domain, without selecting any value lifts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

theorem original_product_total_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : GammaDomainFormula B p a (fun _ => .rv))
    (G : GammaDomainFormula B p b (fun _ => .rv))
    (C : OriginalEulerCertificate B (fun _ : Fin p => .rv) b)
    (hv : ∀ x : X, C.ValidFor hc G (rvValues x.val)) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
      (originalRVTotalFamily X (originalDomainProduct F G)) =
      nativeTorusClass B ^ b * ((C.syntax hc).eulerValue kind : RESDimensionFreeReduction.Ring B) *
        nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X F) := by
  let R := rawParameterProjectionRecode B (Fin.castAdd a : Fin p → Fin (p+a))
  have hC : ∀ u : originalRVTotalFamily X F,
      (C.recode R).ValidFor hc (R.domain G) (rvValues u.val) := by
    intro u
    have hx := ((originalRVTotalFamily_mem X F u.val).mp u.property).1
    have h := (rawParameterProjectionRecode_euler_valid_iff hc (Fin.castAdd a) C G
      (rvValues u.val) (fun j => (u.val j).property))
    exact h.mp (hv ⟨u.val ∘ Fin.castAdd a,hx⟩)
  have he := nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (originalProductTotalBijection X F G)
  have hg := original_gamma_total_value h00 linear hκ hs hr hγ hΓ kind
    (originalRVTotalFamily X F) (R.domain G) (C.recode R) hC
  rw [OriginalEulerCertificate.recode_eulerValue] at hg
  exact he.trans hg

end DiamondIntegral.Section5
