import «section 3».GammaMeasuredPresentationIsomorphism
import «section 3».GammaNativePullbackForms
import «section 3».GammaGroundMeasuredRVGenerators

/-! Concrete class and point evaluations for a density-annotated native
chain. These use the stated principal congruence and literal full keys. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaNativeSpecialClass (U : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :=
  (gammaGroundMeasuredRVSpecialCongruence hc B).mk'
    (gammaGroundMeasuredRVSemiringClass (gammaNativeMeasuredNormalization U ω))

def gammaNativePullbackKeyAt (A : SpecialTransformations.Section5.DefSet (M := M) Set.univ n a)
    (hA : GammaSetDefinable B (carrier A))
    (hAF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject A)))
    (p : A) : Section5.nativeRVGroundDomain (hc := hc)
      (gammaPullbackAt (Set.subset_univ _) A hA hAF) :=
  gammaNativePullbackKeyMap A hA hAF ⟨p.val,p.property⟩

@[simp] theorem gammaNativePullbackKeyAt_val
    (A : SpecialTransformations.Section5.DefSet (M := M) Set.univ n a)
    (hA : GammaSetDefinable B (carrier A))
    (hAF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject A))) (p : A) :
    (gammaNativePullbackKeyAt (hc := hc) A hA hAF p).val = Fin.append (Section2.tupleRV M p.val.1) p.val.2 := rfl

def gammaPresentationLabelAt (U : GammaObjectAt B Set.univ n)
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ n (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ n U.object.obj (normalizedPointSet A)) (p : A) :
    Section5.nativeRVGroundDomain (hc := hc) U :=
  ⟨p.val.2,by
    obtain ⟨u,hu,_⟩ := (h p.val).mp p.property
    exact (Section5.nativeRVGroundDomain_carrier U).ge
      (Eq.mp (congrArg (fun t => t ∈ @DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj)) hu) u.property)⟩

@[simp] theorem gammaPresentationLabelAt_val (U : GammaObjectAt B Set.univ n)
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ n (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ n U.object.obj (normalizedPointSet A)) (p : A) :
    (gammaPresentationLabelAt (hc := hc) U h p).val = p.val.2 := rfl

theorem gammaNativeSpecialClass_hom (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaGroundMeasuredRVHom (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V η)) :
    gammaNativeSpecialClass U ω = gammaNativeSpecialClass V η :=
  congrArg (gammaGroundMeasuredRVSpecialCongruence hc B).mk'
    (gammaGroundMeasuredRVSemiringClass_iso (asIso (show gammaNativeMeasuredNormalization U ω ⟶
      gammaNativeMeasuredNormalization V η from f)))

theorem gammaMeasuredClass_add_toSpecial {k : ℕ}
    (X Y Z : GammaGroundMeasuredRVObject hc B k)
    (h : gammaGroundMeasuredRVClass X + gammaGroundMeasuredRVClass Y = gammaGroundMeasuredRVClass Z) :
    (gammaGroundMeasuredRVSpecialCongruence hc B).mk' (gammaGroundMeasuredRVSemiringClass X) +
      (gammaGroundMeasuredRVSpecialCongruence hc B).mk' (gammaGroundMeasuredRVSemiringClass Y) =
        (gammaGroundMeasuredRVSpecialCongruence hc B).mk' (gammaGroundMeasuredRVSemiringClass Z) := by
  let q := (gammaGroundMeasuredRVSpecialCongruence hc B).mk'
  let f := gammaGroundMeasuredRVKPlusToSemiring (hc := hc) (ground := B) (k := k)
  have H := congrArg (fun x => q (f x)) h
  have hf := f.map_add (gammaGroundMeasuredRVClass X) (gammaGroundMeasuredRVClass Y)
  have hq := q.map_add (f (gammaGroundMeasuredRVClass X)) (f (gammaGroundMeasuredRVClass Y))
  have H' := hq.symm.trans ((congrArg q hf).symm.trans H)
  dsimp only [f] at H'
  rw [gammaGroundMeasuredRVKPlusToSemiring_class,gammaGroundMeasuredRVKPlusToSemiring_class,
    gammaGroundMeasuredRVKPlusToSemiring_class] at H'
  exact H' 

end DiamondIntegral.Section3
