import «section 6».RamifiedApertureValues
import Mathlib.Data.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! The algebraic conservation law for a finite signed value profile.
A point replacement at a named relative increment preserves the profile
summed by cosets of the named value subgroup. This file does not assert
that an arbitrary RV object has a residue Euler profile or that a special
chain has already been converted into such a trace. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Classical

namespace DiamondIntegral.Section6.ApertureValueProfile

variable {W : Type*} [CommGroup W]

def signature (H : Subgroup W) (e : W →₀ ℤ) : (W ⧸ H) →₀ ℤ :=
  e.mapDomain (fun w : W => (w : W ⧸ H))

def replacePoint (e : W →₀ ℤ) (w c : W) : W →₀ ℤ :=
  e - Finsupp.single w 1 + Finsupp.single (w*c) 1

theorem signature_replacePoint (H : Subgroup W) (e : W →₀ ℤ) (w c : W)
    (hc : c ∈ H) : signature H (replacePoint e w c) = signature H e := by
  have he : ((w*c : W) : W ⧸ H) = (w : W ⧸ H) := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [mul_div_cancel_left] using hc
  simp only [signature,replacePoint,Finsupp.mapDomain_add,Finsupp.mapDomain_sub,
    Finsupp.mapDomain_single,he,sub_add_cancel]

inductive Trace (H : Subgroup W) : (W →₀ ℤ) → (W →₀ ℤ) → Prop where
  | refl (e) : Trace H e e
  | replace (e) (w c : W) (hc : c ∈ H) : Trace H e (replacePoint e w c)
  | trans {e f g} : Trace H e f → Trace H f g → Trace H e g

theorem Trace.signature_eq {H : Subgroup W} {e f : W →₀ ℤ} (h : Trace H e f) :
    signature H e = signature H f := by
  induction h with
  | refl => rfl
  | replace e w c hc => exact (signature_replacePoint H e w c hc).symm
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

theorem signature_single_ne (H : Subgroup W) (x y : W) (hxy : (x : W ⧸ H) ≠ y)
    (k : ℤ) (hk : k ≠ 0) :
    signature H (Finsupp.single x k) ≠ signature H (Finsupp.single y k) := by
  intro he
  have h := congrArg (fun e : (W ⧸ H) →₀ ℤ => e (x : W ⧸ H)) he
  simp only [signature,Finsupp.mapDomain_single,Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hxy] at h
  exact hk h

end DiamondIntegral.Section6.ApertureValueProfile

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem ramified_value_not_mem_zpowers (ρ γ : Gamma M) (hρ : 1 < ρ) (hγ : γ^2 = ρ) :
    γ ∉ Subgroup.zpowers ρ := by
  rintro ⟨m,hm⟩
  exact ramified_relative_aperture_values_ne ρ γ hρ hγ 0 m (by simpa only [zpow_zero,one_mul] using hm.symm)

theorem ramified_profile_signature_ne (ρ γ : Gamma M) (hρ : 1 < ρ) (hγ : γ^2 = ρ) :
    ApertureValueProfile.signature (Subgroup.zpowers ρ) (Finsupp.single γ (2 : ℤ)) ≠
      ApertureValueProfile.signature (Subgroup.zpowers ρ) (Finsupp.single 1 (2 : ℤ)) := by
  apply ApertureValueProfile.signature_single_ne
  · intro he
    have hmem := QuotientGroup.eq_iff_div_mem.mp he
    exact ramified_value_not_mem_zpowers ρ γ hρ hγ (by simpa only [div_one] using hmem)
  · norm_num

end DiamondIntegral.Section6
