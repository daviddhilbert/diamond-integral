import «section 3».GammaMeasuredSelectedSchemata
import «section 3».GammaGroundRVFamilyObjects
import «section 5».NativeMixedKeyMaps
import IntegrationSection6.RVLabelHeadPreparations

/-! A head contraction carries an arbitrary Gamma form on retained old
RV labels. This constructs the actual form on the contracted mixed set,
rather than a choice of RV representatives for it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n a r : ℕ}

def gammaPointRVLabelMap (A : DefSet (M := M) S n a)
    (hA : GammaSetDefinable B (carrier A)) (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) r))
    (ρ : Fin r → Fin a) (hLabels : ∀ u : A, u.val.2 ∘ ρ ∈ Q.carrier) :
    GammaGroundMap (Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA) Q :=
  ((gammaGroundRVSelectCoordinates ρ (GammaGroundDefSet.univ hc B (rawRVSpace a))).comp
    (Section5.nativeMixedRVProjection (Section5.nativeGammaPointDomain (carrier A) hA))).corestrict
      (fun u => hLabels ⟨u.val,u.property⟩)

def gammaPointRetainedForm (A : DefSet (M := M) S n a)
    (hA : GammaSetDefinable B (carrier A)) (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) r))
    (ρ : Fin r → Fin a) (hLabels : ∀ u : A, u.val.2 ∘ ρ ∈ Q.carrier)
    (ω : GammaGroundVolumeForm hc B Q) :
    GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA) :=
  ω.comp (gammaPointRVLabelMap A hA Q ρ hLabels)

variable {U : DefSet (M := M) Set.univ (n+1) a}

theorem gammaHeadContractedOldLabels (T : HeadPreparation U) (u : U) :
    (T.contractionMap u).val.2 ∘ headSelectedLabelIndex T (id : Fin a → Fin a) = u.val.2 := by
  have hq : (T.contractionMap u).val = headKey (T.map u).val := headKeyMap_apply T.target (T.map u)
  rw [hq]
  funext j
  simp only [headKey,headSelectedLabelIndex,Function.comp_apply,id_eq,Fin.append_right]
  exact specialRelative_oldLabels T.special u j

theorem gammaHeadContractedLabels_mem (T : HeadPreparation U)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier) (q : T.contractedSet) :
    q.val.2 ∘ headSelectedLabelIndex T (id : Fin a → Fin a) ∈ Q.carrier := by
  obtain ⟨u,rfl⟩ := T.contractionMap_surjective q
  rw [gammaHeadContractedOldLabels]
  exact hLabels u

def gammaHeadContractedForm (T : HeadPreparation U)
    (hTarget : GammaSetDefinable B (carrier T.target))
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    GammaGroundVolumeForm hc B
      (Section5.nativeGammaPointDomain (carrier T.contractedSet) (gamma_headImage T.target hTarget)) :=
  gammaPointRetainedForm T.contractedSet (gamma_headImage T.target hTarget) Q
    (headSelectedLabelIndex T id) (gammaHeadContractedLabels_mem T Q hLabels) ω

theorem gammaHeadContractedForm_apply (T : HeadPreparation U)
    (hTarget : GammaSetDefinable B (carrier T.target))
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) (u : U) :
    gammaHeadContractedForm T hTarget Q hLabels ω ⟨(T.contractionMap u).val,(T.contractionMap u).property⟩ =
      ω ⟨u.val.2,hLabels u⟩ := by
  apply congrArg ω
  apply Subtype.ext
  exact gammaHeadContractedOldLabels T u

end DiamondIntegral.Section3
