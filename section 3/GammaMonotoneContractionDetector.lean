import «section 3».GammaMixedEssentialContractionValues
import «section 3».GammaMixedGroundLiftValues
import «section 3».GammaMeasuredMonotoneBases

/-! The positive-degree additive detector accepts objects and arrows
over a smaller original base while contracting internally over a larger
generated base. Every defining additive relation is checked explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B D : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (hReal : B.real ⊆ D.real) (hGamma : B.gamma ⊆ D.gamma)
variable (C : BaseContext M) (hDC : D.real ⊆ (C.base : Set M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hg : Cardinal.mk D.gamma < C.κ)
variable (hGenerated : VFGammaGeneratedBase D)
variable (δ : Values.Gamma (M := M)) (hδ : δ ∈ D.gamma) (hδ1 : 1 < δ)

def gammaMonotoneContractionInvariant :
    PositiveAdditiveGrothendieck.Invariant
      (gammaGroundMeasuredVFPresentation (hc := hc) (ground := B) C.uncountable.le C.saturated
        ((Cardinal.mk_le_mk_of_subset (hReal.trans hDC)).trans_lt C.small) hv (n+1))
      (A := (gammaGroundMeasuredRVSpecialCongruence hc D).Quotient) where
  toFun U := gammaMixedContractionValue C hDC hv hg hGenerated (U.monoBase hReal hGamma)
  iso := by
    rintro U V ⟨f⟩
    obtain ⟨g,_⟩ := f.property
    exact gammaMixed_essential_contraction_values C hDC hv hg hGenerated δ hδ hδ1
      (g.val.monoBase hReal hGamma) (g.val.preserves_monoBase hReal hGamma g.property).toGeneric
  empty := gammaMixed_empty_contraction_value C hDC hv hg hGenerated _ rfl
  scissor := by
    rintro A E F H ⟨U,X,hX,hA,hE,hF,hH⟩
    subst A
    subst E
    subst F
    subst H
    have hEmpty := gammaMixed_empty_contraction_value C hDC hv hg hGenerated
      ((GammaGroundMeasuredVFData.empty hc B (n+1)).monoBase hReal hGamma) rfl
    have hPart := gammaMixed_binary_partition_values C hDC hv hg hGenerated δ hδ hδ1
      (U.monoBase hReal hGamma) (X.monoBase hReal hGamma) hX
    have hDiff : (U.domain.sdiff X).monoBase hReal hGamma =
        ((U.monoBase hReal hGamma).domain.sdiff (X.monoBase hReal hGamma)) := rfl
    simpa only [gammaMeasuredVF_monoBase_restrict,hDiff,hEmpty,add_zero] using hPart.symm

def gammaMonotoneContractionDetector :
    GammaGroundMeasuredVFKPlus (hc := hc) (ground := B) C.uncountable.le C.saturated
      ((Cardinal.mk_le_mk_of_subset (hReal.trans hDC)).trans_lt C.small) hv (n+1) →+
        (gammaGroundMeasuredRVSpecialCongruence hc D).Quotient :=
  PositiveAdditiveGrothendieck.lift _
    (gammaMonotoneContractionInvariant hReal hGamma C hDC hv hg hGenerated δ hδ hδ1)

theorem gammaMonotoneContractionDetector_class (U : GammaGroundMeasuredVFData hc B (n+1)) :
    gammaMonotoneContractionDetector hReal hGamma C hDC hv hg hGenerated δ hδ hδ1
      (gammaGroundMeasuredVFClass C.uncountable.le C.saturated
        ((Cardinal.mk_le_mk_of_subset (hReal.trans hDC)).trans_lt C.small) hv U) =
      gammaMixedContractionValue C hDC hv hg hGenerated (U.monoBase hReal hGamma) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem gammaMonotoneContractionDetector_lift_class (U : GammaGroundMeasuredRVObject hc B (n+1)) :
    gammaMonotoneContractionDetector hReal hGamma C hDC hv hg hGenerated δ hδ hδ1
      (gammaGroundMeasuredVFClass C.uncountable.le C.saturated
        ((Cardinal.mk_le_mk_of_subset (hReal.trans hDC)).trans_lt C.small) hv (gammaGroundMeasuredObjectLift U)) =
      gammaMeasuredPrincipalValue (U.monoBase hReal hGamma) := by
  rw [gammaMonotoneContractionDetector_class]
  exact gammaMixed_ground_lift_value C hDC hv hg hGenerated δ hδ hδ1 (U.monoBase hReal hGamma)

end DiamondIntegral.Section3
