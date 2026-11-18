import «section 3».GammaNativeProgramRawValues
import «section 3».GammaRectangleRawMeasuredOrders

/-! The existing independent unary rectangle preparations compare all
specified VF-two contraction orders for arbitrary retained Gamma forms.
Same-order comparison supplies both sides of the actual rectangle map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
theorem gamma_vf_two_order_cases (σ : Equiv.Perm (Fin 2)) : σ = Equiv.refl _ ∨ σ = Equiv.swap 0 1 := by
  have h0 : σ 0 = 0 ∨ σ 0 = 1 := by
    by_cases h : σ 0 = 0
    · exact Or.inl h
    · right
      apply Fin.ext
      have hn : (σ 0).val ≠ 0 := fun he => h (Fin.ext he)
      have hl := (σ 0).isLt
      omega
  rcases h0 with h0 | h0
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · have h1 : σ 1 ≠ 0 := fun h => (by decide : (1 : Fin 2) ≠ 0) (σ.injective (h.trans h0.symm))
      apply Fin.ext
      have hn : (σ 1).val ≠ 0 := fun he => h1 (Fin.ext he)
      have hl := (σ 1).isLt
      change (σ 1).val = 1
      omega
  · right
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · have h1 : σ 1 ≠ 1 := fun h => (by decide : (1 : Fin 2) ≠ 0) (σ.injective (h.trans h0.symm))
      apply Fin.ext
      have hn : (σ 1).val ≠ 1 := fun he => h1 (Fin.ext he)
      have hl := (σ 1).isLt
      change (σ 1).val = 0
      omega

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaRectangle_all_order_measured_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {a : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 a}
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (hRect : RectangularRVFibres (carrier A))
    {σ τ : Equiv.Perm (Fin 2)} (T : StandardContraction A σ) (W : StandardContraction A τ)
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin W hW ω) := by
  obtain ⟨F⟩ := independent_rectangle_family_preparations_exists C hNames δ hδ hδ1 A hA hRect
  have hOpp (R : StandardContraction A (Equiv.refl _))
      (S : StandardContraction A (Equiv.swap 0 1))
      (hR : GammaProgramDefinable B R.program) (hS : GammaProgramDefinable B S.program) :
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin R hR ω) =
        gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin S hS ω) := by
    have hL := gammaNativeRawMeasuredContraction_same_order C hBC hv hg δ hδ hδ1 hA hfin
      R F.headContraction hR (F.head_contraction_gamma hA) ω
    have hM := gammaMeasuredPrincipalValue_iso (gammaRectangle_raw_measured_orders C hBC hA hfin F ω)
    have hR := gammaNativeRawMeasuredContraction_same_order C hBC hv hg δ hδ hδ1 hA hfin
      F.tailContraction S (F.tail_contraction_gamma hA) hS ω
    exact hL.trans (hM.trans hR)
  rcases gamma_vf_two_order_cases σ with rfl | rfl
  · rcases gamma_vf_two_order_cases τ with rfl | rfl
    · exact gammaNativeRawMeasuredContraction_same_order C hBC hv hg δ hδ hδ1 hA hfin T W hT hW ω
    · exact hOpp T W hT hW
  · rcases gamma_vf_two_order_cases τ with rfl | rfl
    · exact (hOpp W T hW hT).symm
    · exact gammaNativeRawMeasuredContraction_same_order C hBC hv hg δ hδ hδ1 hA hfin T W hT hW ω

end DiamondIntegral.Section3
