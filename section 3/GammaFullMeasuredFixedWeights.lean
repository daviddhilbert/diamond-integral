import «section 3».GammaFullMeasuredFixedMaps

/-! A VF-fixed measured bijection has Jacobian one at the independent
points. Thus its actual Gamma forms, including their original codes,
agree there. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

theorem gammaGroundForm_eq_of_scalar_eq
    {P Q : Space LRV M} {A : GammaGroundDefSet hc B P} {D : GammaGroundDefSet hc B Q}
    (ω : GammaGroundVolumeForm hc B A) (π : GammaGroundVolumeForm hc B D) (u : A) (v : D)
    (h : (gammaGroundFormValue ω u).val = (gammaGroundFormValue π v).val) : ω u = π v := by
  apply Subtype.ext
  exact (cast_inj (gammaCarrier hc)).mp (show gammaGroundFormValue ω u = gammaGroundFormValue π v from Subtype.ext h)

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G] {k : ℕ}

theorem gammaFullMeasuredFixedVF_form_eq
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U V : GammaGroundMeasuredVFData hc B k} (f : GammaFullMeasuredBijection U V)
    (hVF : ∀ p, (f.map.map p).val.1 = p.val.1)
    (u : U.domain) (hu : AlgebraicIndependent (vfParameterField B.real) u.val.1) :
    U.form u = V.form (f.map.map u) := by
  obtain ⟨J,hJ,hw⟩ := f.measure u hu
  have hOne := gammaVFFixed_jacobian_one hκ hs hr hv f.map.map hVF u hu
  rw [hJ.unique hOne,map_one,mul_one] at hw
  exact gammaGroundForm_eq_of_scalar_eq U.form V.form u (f.map.map u) hw

end DiamondIntegral.Section3
