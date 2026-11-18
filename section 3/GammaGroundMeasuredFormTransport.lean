import «section 3».GammaGroundJacobianDensityForms
import «section 3».GammaGroundInverseForms
import «section 3».GammaFullMeasuredBijections

/-! Transport of arbitrary Gamma forms through an actual mixed
bijection. The construction stays over the original base and is valid
on arbitrary mixed domains, including unary-chain intermediate domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {n r s : ℕ}
variable {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
variable {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n s)}

def gammaGroundTransportedForm (hn : 0 < n) (f : GammaGroundBijection A D)
    (ω : GammaGroundVolumeForm hc B A) : GammaGroundVolumeForm hc B D :=
  (ω.mul (gammaGroundJacobianDensityForm hn f.map).inv).comp f.symm.map

theorem gammaGroundTransportedForm_apply (hn : 0 < n) (f : GammaGroundBijection A D)
    (ω : GammaGroundVolumeForm hc B A) (p : A) :
    gammaGroundFormValue (gammaGroundTransportedForm hn f ω) (f.map p) =
      gammaGroundFormValue ω p * (gammaGroundFormValue (gammaGroundJacobianDensityForm hn f.map) p)⁻¹ := by
  change gammaGroundFormValue (ω.mul (gammaGroundJacobianDensityForm hn f.map).inv)
    (f.map.inverse f.bijective (f.map p)) = _
  rw [GammaGroundMap.inverse_apply]
  rfl

def gammaGroundTransportFullMeasured
    [CharZero (VFType (M := M))] {G : Type} [LinearOrderedCommGroupWithZero G]
    [Valued (VFType (M := M)) G]
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n) (U : GammaGroundMeasuredVFData hc B n)
    (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n s))
    (hfin : ∀ x, {r | (x,r) ∈ D.carrier}.Finite) (f : GammaGroundBijection U.domain D) :
    GammaFullMeasuredBijection U
      (⟨s,D,hfin,gammaGroundTransportedForm hn f U.form⟩ : GammaGroundMeasuredVFData hc B n) where
  map := f
  measure := by
    intro p hp
    obtain ⟨J,hJ,hJ0,hval⟩ := gammaGroundJacobianDensityForm_of_independent hκ hs hr hv hn f p hp
    refine ⟨J,hJ,?_⟩
    change (gammaGroundFormValue U.form p).val =
      (gammaGroundFormValue (gammaGroundTransportedForm hn f U.form) (f.map p)).val * Values.vfValueHom J
    rw [gammaGroundTransportedForm_apply,Values.gamma_val_mul,Values.gamma_val_inv,← hval]
    have hΓ : (gammaGroundFormValue U.form p *
        (gammaGroundFormValue (gammaGroundJacobianDensityForm hn f.map) p)⁻¹) *
        gammaGroundFormValue (gammaGroundJacobianDensityForm hn f.map) p = gammaGroundFormValue U.form p := by
      simp only [mul_assoc,inv_mul_cancel,mul_one]
    have he := congrArg (fun γ : Values.Gamma (M := M) => γ.val) hΓ
    simpa only [Values.gamma_val_mul,Values.gamma_val_inv] using he.symm

end DiamondIntegral.Section3
