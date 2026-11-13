import «section 3».RVResiduePowerKernels
import «section 3».GammaGroundRVDefinableSubgroup
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {G C Γ : Type*} [CommGroup G] [CommGroup C] [CommGroup Γ]

def valueCharacterTwistHom (v : G →* Γ) (ρ : C →* G) (χ : Γ →* C) : G →* G :=
  (ρ.comp (χ.comp v)) * MonoidHom.id G

@[simp] theorem valueCharacterTwistHom_apply (v : G →* Γ) (ρ : C →* G)
    (χ : Γ →* C) (u : G) : valueCharacterTwistHom v ρ χ u = ρ (χ (v u)) * u := rfl

theorem valueCharacterTwistHom_value (v : G →* Γ) (ρ : C →* G)
    (hρ : ∀ c, v (ρ c) = 1) (χ : Γ →* C) (u : G) :
    v (valueCharacterTwistHom v ρ χ u) = v u := by
  rw [valueCharacterTwistHom_apply,map_mul,hρ,one_mul]

def valueCharacterTwistEquiv (v : G →* Γ) (ρ : C →* G)
    (hρ : ∀ c, v (ρ c) = 1) (χ : Γ →* C) : G ≃* G :=
  MulEquiv.ofBijective (valueCharacterTwistHom v ρ χ) (by
    constructor
    · intro u w he
      have hv : v u = v w := by
        have h := congrArg v he
        simpa only [valueCharacterTwistHom_value v ρ hρ] using h
      change ρ (χ (v u)) * u = ρ (χ (v w)) * w at he
      rw [hv] at he
      exact mul_left_cancel he
    · intro y
      let u := (ρ (χ (v y)))⁻¹*y
      have hu : v u = v y := by simp [u,map_mul,map_inv,hρ]
      refine ⟨u,?_⟩
      change ρ (χ (v u))*u = y
      rw [hu]
      exact mul_inv_cancel_left _ _)

@[simp] theorem valueCharacterTwistEquiv_value (v : G →* Γ) (ρ : C →* G)
    (hρ : ∀ c, v (ρ c) = 1) (χ : Γ →* C) (u : G) :
    v (valueCharacterTwistEquiv v ρ hρ χ u) = v u :=
  valueCharacterTwistHom_value v ρ hρ χ u

theorem valueCharacterTwistEquiv_fixed (v : G →* Γ) (ρ : C →* G)
    (hρ : ∀ c, v (ρ c) = 1) (χ : Γ →* C) (u : G) (hu : χ (v u) = 1) :
    valueCharacterTwistEquiv v ρ hρ χ u = u := by
  change ρ (χ (v u))*u = u
  rw [hu,map_one,one_mul]

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvOriginalGroundCharacterTwist (B : Base (M := M))
    (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ) :
    (CanonicalRV.RVSort M)ˣ ≃* (CanonicalRV.RVSort M)ˣ :=
  valueCharacterTwistEquiv rvUnitValueHom residueUnitToRV residueUnitToRV_value_one
    (χ.comp (QuotientGroup.mk' (gammaGroundDefinableRVValues B)))

theorem rvOriginalGroundCharacterTwist_value (B : Base (M := M))
    (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ)
    (u : (CanonicalRV.RVSort M)ˣ) :
    rvUnitValueHom (rvOriginalGroundCharacterTwist B χ u) = rvUnitValueHom u :=
  valueCharacterTwistEquiv_value _ _ _ _ u

theorem rvOriginalGroundCharacterTwist_fixes_ground (B : Base (M := M))
    (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ)
    (u : (CanonicalRV.RVSort M)ˣ) (hu : DefinableClosureAtBase B .rv u.val.val) :
    rvOriginalGroundCharacterTwist B χ u = u := by
  apply valueCharacterTwistEquiv_fixed
  change χ (QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom u)) = 1
  have hv : rvUnitValueHom u ∈ gammaGroundDefinableRVValues B := ⟨u,hu,rfl⟩
  have he := (QuotientGroup.eq_one_iff _).mpr hv
  change QuotientGroup.mk' (gammaGroundDefinableRVValues B) (rvUnitValueHom u) = 1 at he
  rw [he,map_one]

end DiamondIntegral.Section3
