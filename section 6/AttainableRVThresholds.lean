import «section 6».RestrictedCoreVolume

/-! Uniform eventual radius conditions over a bounded RV family can be
met by one actual VF point named over the original VF-generated base.
The entire larger-radius tail satisfies the condition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] {n : ℕ} {S : Set M}

theorem rv_indexed_eventual_radius_named_vf_point
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (v : Valuation (VF M) G) (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    (V : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ v x.val ≠ 1)
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (hNZ : ∀ x ∈ D, ∀ i, GammaParameters.NonzeroRV (x i)) (hDB : RVCodeDoublyBounded D)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P))
    (hEventual : ∀ x ∈ D, ∃ γ, ∀ δ, γ ≤ δ → δ ∈ P x) :
    ∃ c : VF M, ∃ hc0 : c ≠ 0, S.Definable₁ LRV {c.val} ∧
      1 ≤ finiteValue c hc0 ∧ ∀ x ∈ D, ∀ γ, finiteValue c hc0 ≤ γ → γ ∈ P x := by
  obtain ⟨δ,hδ,hδ1,hGood⟩ := rv_indexed_eventual_gamma_named_threshold hc h00 linear hκ hs hsmall hΓ
    D hD hNZ hDB P hP hEventual
  obtain ⟨c,hc0,hcDef,hcVal⟩ := exists_named_vf_above_radius v hv hc h00 V S hV hVS hSV hnt δ hδ1 hδ
  have hδc : δ < finiteValue c hc0 := by
    change δ.val < Values.vfValueHom c
    simpa only [valueHom_eq_value] using hcVal
  exact ⟨c,hc0,hcDef,hδ1.trans hδc.le,fun x hx γ hγ => hGood x hx γ (hδc.trans_le hγ)⟩

end DiamondIntegral.Section6
