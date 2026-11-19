import «section 3».GammaMonotoneContractionDetector
import «section 3».GammaPrincipalBaseReflection
import «section 3».GammaGroundContractionContexts
import «section 3».GammaMeasuredClosureClassLift
import IntegrationSection6.GammaClosureIsomorphisms

/-! The positive-degree reverse measured kernel holds at the exact
original manuscript base. An additive detector runs over its generated
closure and finite geometric reflection eliminates all extra names. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaContextMeasuredDegreeLift_positive_reverse_kernel
    (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (n : ℕ)
    {a b : GammaGroundMeasuredRVKPlus hc C.base (n+1)}
    (h : gammaContextMeasuredDegreeLift C hc hv (n+1) a = gammaContextMeasuredDegreeLift C hc hv (n+1) b) :
    (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' (gammaGroundMeasuredRVKPlusToSemiring a) =
      (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' (gammaGroundMeasuredRVKPlusToSemiring b) := by
  obtain ⟨U,rfl⟩ := gammaGroundMeasuredRVClass_surjective a
  obtain ⟨V,rfl⟩ := gammaGroundMeasuredRVClass_surjective b
  have hU := gammaMeasuredClosureRVClassLift_class C.uncountable C.saturated C.model00 C.small_real C.small_gamma
    (C.fieldBase.gamma_closure_generated C.base.gamma) hv U
  have hV := gammaMeasuredClosureRVClassLift_class C.uncountable C.saturated C.model00 C.small_real C.small_gamma
    (C.fieldBase.gamma_closure_generated C.base.gamma) hv V
  have hLift := hU.symm.trans (h.trans hV)
  let P := closureBase C.base
  let R := gammaGroundContractionContext C
  let hReal := (subset_closureBase C.base).1
  let hGamma := (subset_closureBase C.base).2
  have hPR : P.real ⊆ (R.base : Set M) := fun _ hx => gammaGroundContractionContext_contains C (Or.inl hx)
  have hgP : Cardinal.mk P.gamma < R.κ := closureBase_gamma_small C.uncountable C.base C.small_real C.small_gamma
  let hGenerated := C.fieldBase.gamma_closure_generated C.base.gamma
  obtain ⟨δ,hδ,hδ1⟩ := C.exists_positive_gamma
  let χ := gammaMonotoneContractionDetector (hc := hc) (n := n) hReal hGamma R hPR hv hgP
    hGenerated δ (hGamma hδ) hδ1
  have hχU : χ (gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv
      (gammaGroundMeasuredObjectLift U)) = gammaMeasuredPrincipalValue (U.monoBase hReal hGamma) :=
    gammaMonotoneContractionDetector_lift_class hReal hGamma R hPR hv hgP hGenerated δ (hGamma hδ) hδ1 U
  have hχV : χ (gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv
      (gammaGroundMeasuredObjectLift V)) = gammaMeasuredPrincipalValue (V.monoBase hReal hGamma) :=
    gammaMonotoneContractionDetector_lift_class hReal hGamma R hPR hv hgP hGenerated δ (hGamma hδ) hδ1 V
  have hValue := (hχU.symm.trans (congrArg χ hLift)).trans hχV
  have hOriginal := gammaPrincipal_monoBase_reflect hReal hGamma (closureBaseReduction C.base)
    C.uncountable.le C.saturated C.model00
    (closureBase_real_small C.uncountable C.base C.small_real C.small_gamma) C.small_real hValue
  rw [gammaGroundMeasuredRVKPlusToSemiring_class,gammaGroundMeasuredRVKPlusToSemiring_class]
  exact hOriginal

end DiamondIntegral.Section3
