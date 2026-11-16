import «section 6».MixedFocusCovariance

/-! A named aperture coefficient for any definable bounded focus
family. Finiteness of its VF image is unnecessary: a common lower
valuation bound supplies a nonempty upward-closed choice set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem apertureCoefficients_nonempty_of_lowerBound
    (C : Set (VF M)) (η δ : Gamma M) (hLower : ∀ a ∈ C, η.val ≤ vfValue a) :
    (ApertureCoefficients C δ).Nonempty := by
  obtain ⟨γ,hγ⟩ := exists_gt (max 1 (δ/η))
  obtain ⟨c,hcval⟩ := vfValue_surjective γ.val
  have hc0 : c ≠ 0 := by
    intro he
    exact γ.property (hcval.symm.trans (by rw [he,value_zero]))
  refine ⟨c,hc0,?_,?_⟩
  · exact (show (1 : GammaInfinity M) ≤ γ.val from (le_max_left 1 (δ/η)).trans hγ.le).trans_eq hcval.symm
  · intro a ha
    have hlt : δ < γ*η := (div_lt_iff_lt_mul).mp ((le_max_right 1 (δ/η)).trans_lt hγ)
    have hlt' : δ.val < γ.val*η.val := hlt
    change δ.val < Values.vfValueHom (c*a)
    rw [map_mul]
    change δ.val < vfValue c*vfValue a
    rw [hcval]
    exact hlt'.trans_le (mul_le_mul' le_rfl (hLower a ha))

variable {G : Type} [LinearOrderedCommGroupWithZero G]

theorem exists_named_aperture_coefficient_of_lowerBound
    (v : Valuation (VF M) G) (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ v x.val ≠ 1)
    (C : Set (VF M)) (hC : S.Definable₁ LRV (Subtype.val '' C))
    (η : Gamma M) (hLower : ∀ a ∈ C, η.val ≤ vfValue a) (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}}) :
    ∃ c : VF M, c ≠ 0 ∧ (1 : GammaInfinity M) ≤ vfValue c ∧ S.Definable₁ LRV {c.val} ∧
      ∀ a ∈ C, δ.val < vfValue (c*a) := by
  obtain ⟨c,hcP,hcdef⟩ := exists_named_positive_choice v hv hc h00 V S hV hVS hSV hnt
    (ApertureCoefficients C δ) (apertureCoefficients_definable C hC δ hδ)
    (apertureCoefficients_nonempty_of_lowerBound C η δ hLower)
    (fun _ h => ⟨h.1,h.2.1⟩) (by
      intro a ha b hb hab
      refine ⟨hb,ha.2.1.trans hab,fun z hz => ?_⟩
      have hm := mul_le_mul' hab (le_refl (vfValue z))
      change δ.val < Values.vfValueHom (b*z)
      rw [map_mul]
      have hstart := ha.2.2 z hz
      change δ.val < Values.vfValueHom (a*z) at hstart
      rw [map_mul] at hstart
      exact hstart.trans_le hm)
  exact ⟨c,hcP.1,hcP.2.1,hcdef,hcP.2.2⟩

end DiamondIntegral.Section6
