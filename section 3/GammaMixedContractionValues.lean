import «section 3».GammaRetainedRelativeContractionValues
import «section 3».GammaMeasuredUnaryChains
import Integration7.GammaNamesVolumeContexts

/-! Arbitrary mixed Gamma forms receive a well-defined contraction
value via the checked VF-fixed retained presentation. The value is
independent of that presentation and preserved by every finite full
measured relatively unary chain over the original base. The value is
computed over the code context `gammaMixedCodeContext`, which adjoins the
common real names of `B` to `C.base`; no names hypothesis on `C` is
needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

structure GammaMixedRetainedRepresentation (U : GammaGroundMeasuredVFData hc B (n+1)) where
  data : GammaRetainedMeasuredVFData hc B (n+1)
  map : GammaFullMeasuredBijection U data.toMeasured
  fixesVF : ∀ p, (map.map.map p).val.1 = p.val.1

def gammaMixedRetainedRepresentation (U : GammaGroundMeasuredVFData hc B (n+1)) :
    GammaMixedRetainedRepresentation U := by
  let H := gammaRetainedMeasured_presentation_exists C.uncountable C.saturated C.model00
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hv U
  exact ⟨H.choose,H.choose_spec.choose,H.choose_spec.choose_spec⟩

variable (hg : Cardinal.mk B.gamma < C.κ)

/-- The code context used for mixed contraction values: `C.base` with the
common real names of `B` adjoined. Only a code set; the objects are
Gamma-ground objects over `B`. -/
def gammaMixedCodeContext : BaseContext M := gammaNamesContainingVolumeContext C B hBC hg

theorem gammaMixedCodeContext_real : B.real ⊆ ((gammaMixedCodeContext C hBC hg).base : Set M) :=
  fun _ hx => gamma_names_containing_volume_context_contains C B hBC hg (Or.inl (hBC hx))

theorem gammaMixedCodeContext_names :
    commonRealNames B ⊆ ((gammaMixedCodeContext C hBC hg).base : Set M) :=
  fun _ hx => gamma_names_containing_volume_context_contains C B hBC hg (Or.inr hx)

theorem gammaMixedCodeContext_gamma : Cardinal.mk B.gamma < (gammaMixedCodeContext C hBC hg).κ := hg

variable (hGenerated : VFGammaGeneratedBase B)

def gammaMixedContractionValue (U : GammaGroundMeasuredVFData hc B (n+1)) :=
  (gammaMixedRetainedRepresentation (gammaMixedCodeContext C hBC hg) (gammaMixedCodeContext_real C hBC hg) hv U).data.contractionValue
    (gammaMixedCodeContext C hBC hg) (gammaMixedCodeContext_real C hBC hg)
    (gammaMixedCodeContext_names C hBC hg) hGenerated

variable (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)

include δ hδ hδ1 in
theorem gammaMixed_contraction_value_of_presentation
    (U : GammaGroundMeasuredVFData hc B (n+1)) (P : GammaRetainedMeasuredVFData hc B (n+1))
    (E : GammaFullMeasuredBijection U P.toMeasured) (hE : ∀ p, (E.map.map p).val.1 = p.val.1) :
    gammaMixedContractionValue C hBC hv hg hGenerated U = P.contractionValue (gammaMixedCodeContext C hBC hg) (gammaMixedCodeContext_real C hBC hg)
      (gammaMixedCodeContext_names C hBC hg) hGenerated := by
  let C' := gammaMixedCodeContext C hBC hg
  have hBC' := gammaMixedCodeContext_real C hBC hg
  have hNames' := gammaMixedCodeContext_names C hBC hg
  have hg' := gammaMixedCodeContext_gamma C hBC hg
  let hr := (Cardinal.mk_le_mk_of_subset hBC').trans_lt C'.small
  let R := gammaMixedRetainedRepresentation C' hBC' hv U
  let K := (R.map.symm C'.uncountable.le C'.saturated hr hv).comp C'.uncountable.le C'.saturated hr hv E
  have hInv (p : R.data.toMeasured.domain) : (R.map.map.symm.map p).val.1 = p.val.1 := by
    have h := R.map.map.map.apply_inverse R.map.map.bijective p
    exact (R.fixesVF (R.map.map.symm.map p)).symm.trans (congrArg (fun q => q.val.1) h)
  apply gammaRetained_relative_contraction_values C' hBC' hv hg' hNames' hGenerated δ hδ hδ1 K 0
  intro p j _
  exact (congrFun (hE (R.map.map.symm.map p)) j).trans (congrFun (hInv p) j)

include δ hδ hδ1 in
theorem gammaMixed_relative_contraction_values
    {U V : GammaGroundMeasuredVFData hc B (n+1)} (F : GammaFullMeasuredBijection U V)
    (i : Fin (n+1)) (hi : ∀ p, ∀ j, j ≠ i → (F.map.map p).val.1 j = p.val.1 j) :
    gammaMixedContractionValue C hBC hv hg hGenerated U =
      gammaMixedContractionValue C hBC hv hg hGenerated V := by
  let C' := gammaMixedCodeContext C hBC hg
  have hBC' := gammaMixedCodeContext_real C hBC hg
  have hNames' := gammaMixedCodeContext_names C hBC hg
  have hg' := gammaMixedCodeContext_gamma C hBC hg
  let hr := (Cardinal.mk_le_mk_of_subset hBC').trans_lt C'.small
  let P := gammaMixedRetainedRepresentation C' hBC' hv U
  let Q := gammaMixedRetainedRepresentation C' hBC' hv V
  let K := ((P.map.symm C'.uncountable.le C'.saturated hr hv).comp C'.uncountable.le C'.saturated hr hv F).comp
    C'.uncountable.le C'.saturated hr hv Q.map
  have hInv (p : P.data.toMeasured.domain) : (P.map.map.symm.map p).val.1 = p.val.1 := by
    have h := P.map.map.map.apply_inverse P.map.map.bijective p
    exact (P.fixesVF (P.map.map.symm.map p)).symm.trans (congrArg (fun q => q.val.1) h)
  apply gammaRetained_relative_contraction_values C' hBC' hv hg' hNames' hGenerated δ hδ hδ1 K i
  intro p j hj
  exact (congrFun (Q.fixesVF (F.map.map (P.map.map.symm.map p))) j).trans
    ((hi (P.map.map.symm.map p) j hj).trans (congrFun (hInv p) j))

include δ hδ hδ1 in
theorem gammaMixed_unary_chain_contraction_values
    {U V : GammaGroundMeasuredVFData hc B (n+1)} (T : GammaMeasuredUnaryChain U V) :
    gammaMixedContractionValue C hBC hv hg hGenerated U =
      gammaMixedContractionValue C hBC hv hg hGenerated V := by
  induction T with
  | nil U => rfl
  | cons i f hi tail ih =>
    exact (gammaMixed_relative_contraction_values C hBC hv hg hGenerated δ hδ hδ1 f i hi).trans ih

end DiamondIntegral.Section3
