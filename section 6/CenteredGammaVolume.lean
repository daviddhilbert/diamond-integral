import «section 6».CenteredDiscVolumeComparison

/-! The radius/Jacobian identity on centered open discs in the paper's
actual Gamma quotient. Radius representatives and the constant Jacobian
value need not be named over S. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] {r s : ℕ} {S : Set M}

theorem centeredGammaDisc_iff_valuation (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    (a d x : VF M) (hd : d ≠ 0) :
    x ∈ centeredGammaDisc a (finiteValue d hd) ↔ v (x-a) < v d :=
  (rawOpenBall_iff_centeredGammaDisc a d x hd).symm.trans (mem_rawOpenBall_iff v hv a d x hd)

theorem centered_disc_gamma_volume_comparison [CharZero (VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ) (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S}
    {B : DefSet (rawMixedSpace (M := M) 1 s) S}
    (f : Map A B) (hf : Function.Bijective f)
    (a b d e : VF M) (hd : d ≠ 0) (he : e ≠ 0)
    (hA : ∀ x : Fin 1 → VF M, (∃ p : A, p.val.1 = x) ↔ x 0 ∈ centeredGammaDisc a (finiteValue d hd))
    (hB : ∀ x : Fin 1 → VF M, (∃ p : B, p.val.1 = x) ↔ x 0 ∈ centeredGammaDisc b (finiteValue e he))
    (η : Gamma M) (Z : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hZ : vfDim (rawRVSpace (M := M) 1) Z < 1)
    (hconst : ∀ p : A, p.val ∉ Z.carrier → ∃ J, HasMixedVFJacobianAt f p J ∧ vfValue J = η.val) :
    finiteValue e he = η*finiteValue d hd := by
  obtain ⟨c,hc0,hcη⟩ := gamma_has_vf_representative η
  have hconst' (p : A) (hp : p.val ∉ Z.carrier) :
      ∃ J, HasMixedVFJacobianAt f p J ∧ v J = v c := by
    obtain ⟨J,hJ,hη⟩ := hconst p hp
    refine ⟨J,hJ,(Values.vf_value_eq_iff v hv J c).mp ?_⟩
    change Values.vfValueHom J = Values.vfValueHom c
    rw [hcη]
    simpa only [valueHom_eq_value] using hη
  have hVolume := centered_unary_disc_volume_comparison hc hκ hs h00 hsmall v hv f hf a b d e hd he
    (fun x => (hA x).trans (centeredGammaDisc_iff_valuation v hv a d (x 0) hd))
    (fun x => (hB x).trans (centeredGammaDisc_iff_valuation v hv b e (x 0) he)) c hc0 Z hZ hconst'
  have hMul : v (c*d) = v e := by
    rw [map_mul]
    exact (eq_div_iff (v.ne_zero_iff.mpr hd)).mp hVolume
  have hGamma := (Values.vf_value_eq_iff v hv (c*d) e).mpr hMul
  apply Subtype.ext
  change Values.vfValueHom e = η.val*Values.vfValueHom d
  rw [← hcη,← map_mul]
  exact hGamma.symm

end DiamondIntegral.Section6
