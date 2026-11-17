import «section 3».GammaPreparedMeasuredGeometryComparison
import IntegrationSection6.GammaPreparedIndexPresentation
import IntegrationSection6.GammaPreparedIndexValues
import Integration7.GammaEssentialIndexDomains

/-! A named witness predicate for the existing prepared principal
comparison. It retains the exact geometric preparation, original-base
row agreements and measured indexed objects. -/set_option autoImplicit false
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b k : ℕ}

def GammaPreparedMeasuredFamilyComparison
    (C₀ : BaseContext M) (A : SpecialTransformations.Section5.DefSet (M := M) (C₀.base : Set M) p 0)
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .vf))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .vf)) : Prop :=
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ l : ℕ, ∃ Z : SpecialTransformations.Section5.DefSet (M := M) (D.base : Set M) p l,
    ∃ T : SpecialBijection (extendBase A hC₀D) Z, ∃ hT : GammaChainDefinable B T.chain,
    ∃ hZ : IsRVPullback (carrier Z), ∃ BP : PreparedIndexPresentation B Z,
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G.toRVTemplate
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      let K := GammaParameterRecode.prepared T hT
      ∃ hF : ∀ t ∈ essentialIndexDomain BP, (F.recode K).valid (rvValues t),
      ∃ hG : ∀ t ∈ essentialIndexDomain BP, (G.recode K).valid (rvValues t),
        ∀ (P : (F.recode K).object.IndexedPresentation (essentialIndexPresentation BP))
          (Q : (G.recode K).object.IndexedPresentation (essentialIndexPresentation BP)),
          gammaMeasuredPrincipalValue ((F.recode K).indexedObject (essentialIndexPresentation BP) hF P) =
            gammaMeasuredPrincipalValue ((G.recode K).indexedObject (essentialIndexPresentation BP) hG Q)

theorem gammaPreparedMeasuredFamilyComparison_of_generic
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C₀.base : Set M) p 0)
    (hA : GammaSetDefinable B (carrier A))
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .vf))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .vf))
    (hWitness : ∀ x : Fin p → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaMeasuredRelationSchema F G, H.valid (vfValues x)) :
    GammaPreparedMeasuredFamilyComparison C₀ A F G :=
  gammaGeneric_prepared_measured_geometry_comparison hκ hs h00 hr hg C₀ hBC₀ A hA F G hWitness

end DiamondIntegral.Section3
