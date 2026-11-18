import «section 3».GammaSelectedLiftCarriers
import IntegrationSection6.GammaHeadSelectedFiniteness
import Integration7.NativeSelectedRVVFTailLifts

/-! The full selected RV object of a unary head contraction lifts to
its actual canonical head with the remaining selected labels realized
by fixed VF tails. Zero head and tail coordinates remain present. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section5.pointSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {a k : ℕ} {A : DefSet (M := M) S 1 a}
variable (T : HeadPreparation A) (ρ : Fin k → Fin a)
variable (P : GammaFiniteGraphPresentation B (1+T.arity) (1+k)
  {r | (Fin.elim0,r) ∈ carrier T.contractedSet}
  (fun r y => (Fin.elim0,r) ∈ carrier T.contractedSet ∧ r ∘ headVolumeIndex T ρ = y))

theorem gammaHeadSelectedLift_carrier :
    (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain.carrier =
      carrier (nativeSelectedRVVFTailLift hc T.liftSet (headSelectedLabelIndex T ρ)) := by
  ext q
  rw [gammaSelectedLift_mem T.contractedSet (headVolumeIndex T ρ) P]
  rw [native_selected_rv_vf_tail_lift_carrier]
  have hDrop : dropHead id (q.1 ∘ Fin.castAdd k,q.2) = (Fin.elim0,q.2) :=
    Prod.ext (Subsingleton.elim _ _) rfl
  have hCanon := T.liftSet_exact (q.1 ∘ Fin.castAdd k,q.2)
  rw [hDrop] at hCanon
  rw [hCanon]
  constructor
  · rintro ⟨hC,hVol⟩
    refine ⟨⟨hC,?_⟩,?_⟩
    · have hh := congrFun hVol (Fin.castAdd k (0 : Fin 1))
      simp only [headVolumeIndex,Function.comp_apply,Fin.append_left] at hh
      exact hh.symm
    · funext j
      have ht := congrFun hVol (Fin.natAdd 1 j)
      simp only [headVolumeIndex,Function.comp_apply,Fin.append_right] at ht
      exact ht
  · rintro ⟨⟨hC,hHead⟩,hTail⟩
    refine ⟨hC,?_⟩
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simp only [headVolumeIndex,Function.comp_apply,Fin.append_left]
      exact hHead.symm
    · have ht := congrFun hTail i
      simp only [headVolumeIndex,Function.comp_apply,Fin.append_right]
      exact ht

end DiamondIntegral.Section3
