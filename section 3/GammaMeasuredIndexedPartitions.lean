import «section 3».GammaMeasuredIndexedRestrictions
import «section 3».GammaNativeMeasuredScissors
import «section 3».GammaMeasuredIndexedGeometry
import IntegrationSection6.GammaGraphPresentationRestriction
import IntegrationSection6.GammaUniversalSubsets
import IntegrationSection6.IndexedSetPartitions

/-! A definable partition of the retained RV index splits the actual
measured class, with its original Gamma density on both regions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaMeasuredRVSchema.indexed_binary_value
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (E : Set (Fin p → RV (M := M))) (hET : E ⊆ T)
    (hEΓ : GammaSetDefinable B {t : Point (M := M) 0 p | t.2 ∈ E})
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (P : F.object.IndexedPresentation BP) :
    let BPA := BP.restrictDomain E hET hEΓ
    let BPC := BP.restrictDomain (T \ E) (fun _ h => h.1) ((gammaLogicInput B).sdiff BP.domain_graph hEΓ)
    ∀ (PA : F.object.IndexedPresentation BPA) (PC : F.object.IndexedPresentation BPC),
      gammaMeasuredPrincipalValue (F.indexedObject BP hF P) =
        gammaMeasuredPrincipalValue (F.indexedObject BPA (fun t ht => hF t (hET ht)) PA) +
          gammaMeasuredPrincipalValue (F.indexedObject BPC (fun t ht => hF t ht.1) PC) := by
  intro BPA BPC PA PC
  let U := gammaUniversalObject P.toGamma
  let ω := F.indexedForm BP hF P
  obtain ⟨A,hA⟩ := exists_gammaUniversalDefSet
    (indexedDomain E (fun t => F.object.rowDomain (rvValues t))) (F.object.indexed_domain_graph BPA)
  have hΓA : GammaSetDefinable B {w : Point (M := M) 0 (p+a) |
      w.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ A} := by
    convert F.object.indexed_domain_graph BPA using 1
    exact Set.ext (fun w => Set.ext_iff.mp hA w.2)
  have hSub : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ A ⊆
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj) := by
    intro w hw
    exact P.domain_eq.ge (indexedDomain_mono hET _ (hA.le hw))
  let C := @complement M N Set.univ ((d+k)+1) U.object.obj A
  have hC : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ C =
      indexedDomain (T \ E) (fun t => F.object.rowDomain (rvValues t)) := by
    change (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj) \
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ A) = _
    have hP : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ
        (rvObjectDomain U.object.obj) = indexedDomain T (fun t => F.object.rowDomain (rvValues t)) := P.domain_eq
    rw [hP,hA,indexedDomain_sdiff]
  obtain ⟨eA⟩ := F.indexedRestrictionChart BP BPA (BP.restrictDomain_totalVolume E hET hEΓ)
    hF (fun t ht => hF t (hET ht)) P PA A hSub hA hΓA
  obtain ⟨eC⟩ := F.indexedRestrictionChart BP BPC
    (BP.restrictDomain_totalVolume (T \ E) (fun _ h => h.1) ((gammaLogicInput B).sdiff BP.domain_graph hEΓ))
    hF (fun t ht => hF t ht.1) P PC C (@complement_subset M N hN Set.univ ((d+k)+1) U.object.obj A)
    hC ((gammaLogicInput B).sdiff U.domain_graph hΓA)
  have hScissor := gammaNativeMeasuredClass_scissor U A hSub hΓA ω
  have hInside := gammaGroundMeasuredRVClass_iso (asIso eA)
  have hOutside := gammaGroundMeasuredRVClass_iso (asIso eC)
  apply gammaMeasuredPrincipalValue_add
  exact hScissor.symm.trans (congrArg₂ (· + ·) hInside hOutside)

end DiamondIntegral.Section3
