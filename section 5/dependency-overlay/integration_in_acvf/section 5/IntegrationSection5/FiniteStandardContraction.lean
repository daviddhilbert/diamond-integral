import IntegrationSection5.FiniteNumbered
import IntegrationSection5.StandardSpecialPresentation
import IntegrationSection5.StandardContractionGammaNormalization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
open CategoryTheory
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
open SpecialTransformations.Section3
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m : ℕ}
variable {A : DefSet (M := M) S n m} {σ : Equiv.Perm (Fin n)}

namespace StandardContraction

theorem normalized_finite_volume {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk G.real < κ) (hGS : G.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable G (carrier A)) (hC : GammaProgramDefinable G C.program)
    (hFinite : FiniteMixedRVFibres (carrier A)) :
    Map.FiniteFibres (rvObjectVolume C.normalizedObject) :=
  rv_volume_finite_of_lift_finite C.normalizedObject
    (GammaIso.finite_mixed_rv_fibres hκ hs hsmall (C.gammaNormalizedLiftIso hGS hA hC) hFinite)

def normalizedFiniteObject {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk G.real < κ) (hGS : G.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable G (carrier A)) (hC : GammaProgramDefinable G C.program)
    (hFinite : FiniteMixedRVFibres (carrier A)) : FiniteRVObject S n :=
  ⟨C.normalizedObject,C.normalized_finite_volume hκ hs hsmall hGS hA hC hFinite⟩

def gammaNormalizedFiniteObject {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk G.real < κ) (hGS : G.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable G (carrier A)) (hC : GammaProgramDefinable G C.program)
    (hFinite : FiniteMixedRVFibres (carrier A)) : GammaRVFiniteObject G n where
  toGammaRVObject := C.gammaNormalizedObject hGS (gamma_program_final_set C.program hC)
  finite_volume := C.normalized_finite_volume hκ hs hsmall hGS hA hC hFinite

def finiteNormalizationIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk G.real < κ) (hGS : G.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable G (carrier A)) (hC : GammaProgramDefinable G C.program)
    (hFinite : FiniteMixedRVFibres (carrier A)) :
    C.finiteObject hκ hs hsmall hGS hA hC hFinite ≅ C.normalizedFiniteObject hκ hs hsmall hGS hA hC hFinite :=
  ObjectProperty.isoMk _ C.normalizationIso

end StandardContraction

/-- Definition5.5 in the author's finite-volume scope, retaining the actual global-special presentation. -/
theorem lemma_5_5_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real) (hGS : G.real ⊆ S)
    (A : DefSet (M := M) S n m) (hA : GammaSetDefinable G (carrier A))
    (hFinite : FiniteMixedRVFibres (carrier A)) (σ : Equiv.Perm (Fin n)) :
    ∃ C : StandardContraction A σ, ∃ hC : GammaProgramDefinable G C.program,
      Nonempty (StandardSpecialPresentation G C) ∧
      Map.FiniteFibres (rvObjectVolume C.contractionObject) ∧
      Map.FiniteFibres (rvObjectVolume C.normalizedObject) ∧
      Nonempty (C.finiteObject hκ hs hsmall hGS hA hC hFinite ≅
        C.normalizedFiniteObject hκ hs hsmall hGS hA hC hFinite) := by
  obtain ⟨C,hC,hSpecial⟩ := standard_contraction_exists_with_special_presentation hs h00 G hsmall F hGS A hA σ
  exact ⟨C,hC,hSpecial,C.finite_volume hκ hs hsmall hGS hA hC hFinite,
    C.normalized_finite_volume hκ hs hsmall hGS hA hC hFinite,
    ⟨C.finiteNormalizationIso hκ hs hsmall hGS hA hC hFinite⟩⟩

end IntegrationInACVF.Section5
