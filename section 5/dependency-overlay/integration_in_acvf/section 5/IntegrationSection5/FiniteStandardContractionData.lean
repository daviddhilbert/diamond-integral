import IntegrationSection5.FiniteStandardContraction

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

/-- The actual standard contraction data in RV[n], over an internally constructed real presentation. -/
structure FiniteStandardContractionData (G : GammaParameters.Base (M := M)) {n m : ℕ}
    (A : Set (Point (M := M) n m)) (σ : Equiv.Perm (Fin n)) where
  codes : Set M
  real_contains : G.real ⊆ codes
  source : DefSet (M := M) codes n m
  source_eq : carrier source = A
  source_gamma : GammaSetDefinable G (carrier source)
  contraction : StandardContraction source σ
  program_gamma : GammaProgramDefinable G contraction.program
  finite_volume : Map.FiniteFibres (rvObjectVolume contraction.contractionObject)
  finite_normalized_volume : Map.FiniteFibres (rvObjectVolume contraction.normalizedObject)
  special_presentation : StandardSpecialPresentation G contraction

namespace FiniteStandardContractionData
variable {G : GammaParameters.Base (M := M)} {n m : ℕ} {A : Set (Point (M := M) n m)} {σ : Equiv.Perm (Fin n)}

def rvObject (D : FiniteStandardContractionData G A σ) : FiniteRVObject D.codes n :=
  ⟨D.contraction.contractionObject,D.finite_volume⟩

def normalizedRVObject (D : FiniteStandardContractionData G A σ) : FiniteRVObject D.codes n :=
  ⟨D.contraction.normalizedObject,D.finite_normalized_volume⟩

def normalizationIso (D : FiniteStandardContractionData G A σ) : D.rvObject ≅ D.normalizedRVObject :=
  ObjectProperty.isoMk _ D.contraction.normalizationIso

def gammaObject (D : FiniteStandardContractionData G A σ) : GammaRVFiniteObject G n where
  toGammaRVObject := D.contraction.gammaNormalizedObject D.real_contains
    (gamma_program_final_set D.contraction.program D.program_gamma)
  finite_volume := D.finite_normalized_volume

def naturalLiftIso (D : FiniteStandardContractionData G A σ) :
    GammaIso G (carrier D.source) D.gammaObject.toGammaRVObject.lift :=
  D.contraction.gammaNormalizedLiftIso D.real_contains D.source_gamma D.program_gamma

end FiniteStandardContractionData

theorem lemma_5_5 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real) {n m : ℕ}
    (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable G A)
    (hFinite : FiniteMixedRVFibres A) (σ : Equiv.Perm (Fin n)) :
    Nonempty (FiniteStandardContractionData G A σ) := by
  obtain ⟨d,t,ht,H,hH⟩ := gammaPresentationInput G A hA
  let S0 := G.real ∪ Set.range (GammaParameters.rawTuple t)
  have hHG : GammaSetDefinable G (carrier H) := hH.symm ▸ hA
  have hHF : FiniteMixedRVFibres (carrier H) := hH.symm ▸ hFinite
  obtain ⟨C,hC,⟨P⟩,hV,hVN,hIso⟩ := lemma_5_5_finite hκ hs h00 G hsmall F
    (S := S0) Set.subset_union_left H hHG hHF σ
  exact ⟨{
    codes := S0
    real_contains := Set.subset_union_left
    source := H
    source_eq := hH
    source_gamma := hHG
    contraction := C
    program_gamma := hC
    finite_volume := hV
    finite_normalized_volume := hVN
    special_presentation := P }⟩

end IntegrationInACVF.Section5
