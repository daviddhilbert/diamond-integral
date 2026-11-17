import «section 3».GammaSurjectiveMapDescent
import «section 3».GammaNativeMeasuredLifts
import «section 5».NativeMixedKeyMaps
import IntegrationSection6.FiniteGammaObjects

/-! An RV-pullback's full key carries every Gamma form constant on the
old RV labels. The descent is over the original ground and uses the
literal native pullback domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
variable (A : SpecialTransformations.Section5.DefSet (M := M) Set.univ n a)
variable (hA : GammaSetDefinable B (carrier A))
variable (hAF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject A)))

def gammaNativePullbackKeyMap : GammaGroundMap (Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA)
    (Section5.nativeRVGroundDomain (gammaPullbackAt (Set.subset_univ _) A hA hAF)) :=
  (Section5.nativeMixedFullKeyMap (Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA)).corestrict
    (fun p => by
      apply (Section5.nativeRVGroundDomain_carrier _).ge
      exact ⟨⟨p.val,p.property⟩,rfl⟩)

theorem gammaNativePullbackKeyMap_surjective :
    Function.Surjective (gammaNativePullbackKeyMap (hc := hc) A hA hAF) := by
  intro u
  obtain ⟨p,hp⟩ := (Section5.nativeRVGroundDomain_carrier _).le u.property
  exact ⟨⟨p.val,p.property⟩,Subtype.ext hp⟩

theorem gammaNativePullbackKeyMap_old_labels
    (p q : Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA)
    (hpq : gammaNativePullbackKeyMap A hA hAF p = gammaNativePullbackKeyMap A hA hAF q) :
    p.val.2 = q.val.2 := by
  have h := congrArg (fun u => u.val ∘ Fin.natAdd n) hpq
  change Fin.append (Section2.tupleRV M p.val.1) p.val.2 ∘ Fin.natAdd n =
    Fin.append (Section2.tupleRV M q.val.1) q.val.2 ∘ Fin.natAdd n at h
  simpa only [Function.comp_def,Fin.append_right] using h

def gammaNativePullbackForm
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA))
    (hω : ∀ p q, p.val.2 = q.val.2 → ω p = ω q) :
    GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (gammaPullbackAt (Set.subset_univ _) A hA hAF)) :=
  gammaGroundSurjectiveDescent (gammaNativePullbackKeyMap A hA hAF)
    (gammaNativePullbackKeyMap_surjective A hA hAF) ω
    (fun p q hpq => hω p q (gammaNativePullbackKeyMap_old_labels A hA hAF p q hpq))

theorem gammaNativePullbackForm_apply
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA))
    (hω : ∀ p q, p.val.2 = q.val.2 → ω p = ω q)
    (p : Section5.nativeGammaPointDomain (carrier A) hA) :
    gammaNativePullbackForm A hA hAF ω hω (gammaNativePullbackKeyMap A hA hAF p) = ω p :=
  gammaGroundSurjectiveDescent_apply _ _ _ _ p

end DiamondIntegral.Section3
