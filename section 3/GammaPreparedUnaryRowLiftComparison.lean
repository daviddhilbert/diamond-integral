import «section 3».GammaPreparedMeasuredGeometryComparison
import «section 3».GammaUnaryLiftRowComparisons
import IntegrationSection6.GammaPreparedIndexPresentation
import IntegrationSection6.GammaPreparedIndexValues
import Integration7.GammaEssentialIndexDomains

/-! Full measured unary row-lift comparisons at generic original-base
VF tuples give a prepared comparison in the stated principal quotient.
No resolved base or RV density representative is used. -/set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G₀ : Type} [LinearOrderedCommGroupWithZero G₀] [Valued (Section2.VF M) G₀]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

theorem gammaGeneric_prepared_unary_row_lift_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C₀.base : Set M) p 0)
    (hA : GammaSetDefinable B (carrier A))
    (F : GammaMeasuredRVSchema hc B p a 1 (fun _ => .vf))
    (G : GammaMeasuredRVSchema hc B p b 1 (fun _ => .vf))
    (hRows : ∀ x : Fin p → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      gammaUnaryMeasuredRowLiftComparison F G (vfValues x)) :
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ l : ℕ, ∃ Z : SpecialTransformations.Section5.DefSet (M := M) (D.base : Set M) p l,
    ∃ T : SpecialBijection (extendBase A hC₀D) Z, ∃ hT : GammaChainDefinable B T.chain,
    ∃ hZ : IsRVPullback (carrier Z), ∃ BP : PreparedIndexPresentation B Z,
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F.essential.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G.essential.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      let K := GammaParameterRecode.prepared T hT
      ∃ hF : ∀ t ∈ essentialIndexDomain BP, (F.essential.recode K).valid (rvValues t),
      ∃ hG : ∀ t ∈ essentialIndexDomain BP, (G.essential.recode K).valid (rvValues t),
        ∀ (P : (F.essential.recode K).object.IndexedPresentation (essentialIndexPresentation BP))
          (Q : (G.essential.recode K).object.IndexedPresentation (essentialIndexPresentation BP)),
          gammaMeasuredPrincipalValue ((F.essential.recode K).indexedObject (essentialIndexPresentation BP) hF P) =
            gammaMeasuredPrincipalValue ((G.essential.recode K).indexedObject (essentialIndexPresentation BP) hG Q) := by
  exact gammaGeneric_prepared_measured_geometry_comparison hκ.le hs h00 hr hg C₀ hBC₀ A hA F.essential G.essential
    (fun x hx => gammaMeasured_unary_raw_row_witness hκ hs h00 hr hg hv δ hδ hδ1 F G (vfValues x) (hRows x hx))

end DiamondIntegral.Section3
