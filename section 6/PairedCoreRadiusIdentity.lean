import «section 6».CenteredGammaVolume

/-! The exact exceptional-core radius identity, allowing unnamed Gamma
radii. The equality is in the actual value group and includes constant
source and target volume forms; all analytic exceptions are explicit. -/

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

theorem paired_centered_disc_radius_identity [CharZero (VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ) (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S}
    {B : DefSet (rawMixedSpace (M := M) 1 s) S}
    (f : Map A B) (hf : Function.Bijective f)
    (a b : VF M) (α β η : Gamma M)
    (hA : ∀ x : Fin 1 → VF M, (∃ p : A, p.val.1 = x) ↔ x 0 ∈ centeredGammaDisc a α)
    (hB : ∀ x : Fin 1 → VF M, (∃ p : B, p.val.1 = x) ↔ x 0 ∈ centeredGammaDisc b β)
    (Z : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hZ : vfDim (rawRVSpace (M := M) 1) Z < 1)
    (hconst : ∀ p : A, p.val ∉ Z.carrier → ∃ J, HasMixedVFJacobianAt f p J ∧ vfValue J = η.val) :
    β = η*α := by
  obtain ⟨d,hd,hdα⟩ := gamma_has_vf_representative α
  obtain ⟨e,he,heβ⟩ := gamma_has_vf_representative β
  have hdΓ : finiteValue d hd = α := Subtype.ext hdα
  have heΓ : finiteValue e he = β := Subtype.ext heβ
  have hA' : ∀ x : Fin 1 → VF M, (∃ p : A, p.val.1 = x) ↔ x 0 ∈ centeredGammaDisc a (finiteValue d hd) := by
    simpa only [hdΓ] using hA
  have hB' : ∀ x : Fin 1 → VF M, (∃ p : B, p.val.1 = x) ↔ x 0 ∈ centeredGammaDisc b (finiteValue e he) := by
    simpa only [heΓ] using hB
  simpa only [hdΓ,heΓ] using centered_disc_gamma_volume_comparison hc hκ hs h00 hsmall v hv
    f hf a b d e hd he hA' hB' η Z hZ hconst

theorem paired_core_volume_forms_identity [CharZero (VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ) (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S}
    {B : DefSet (rawMixedSpace (M := M) 1 s) S}
    (f : Map A B) (hf : Function.Bijective f)
    (a b : VF M) (α β ω σ : Gamma M)
    (hA : ∀ x : Fin 1 → VF M, (∃ p : A, p.val.1 = x) ↔ x 0 ∈ centeredGammaDisc a α)
    (hB : ∀ x : Fin 1 → VF M, (∃ p : B, p.val.1 = x) ↔ x 0 ∈ centeredGammaDisc b β)
    (Z : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hZ : vfDim (rawRVSpace (M := M) 1) Z < 1)
    (hconst : ∀ p : A, p.val ∉ Z.carrier →
      ∃ J, HasMixedVFJacobianAt f p J ∧ vfValue J = (ω/σ).val) :
    ω*α = σ*β := by
  have hRadius := paired_centered_disc_radius_identity hc hκ hs h00 hsmall v hv f hf
    a b α β (ω/σ) hA hB Z hZ hconst
  rw [hRadius]
  simp only [div_eq_mul_inv,mul_left_comm,mul_assoc,mul_inv_cancel_left]

end DiamondIntegral.Section6
