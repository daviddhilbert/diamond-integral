import «section 3».GammaNativeRawMeasuredIsomorphisms

/-! The actual coordinate and old-label identities in the RV-density
geometric exports preserve every retained Gamma form. The complete
Gamma graph stays over the original ground throughout normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

theorem gammaNativeRVGroundVolume_gamma (U : GammaObjectAt B Set.univ n)
    (u : Section5.nativeRVGroundDomain (hc := hc) U) :
    (Section5.nativeRVGroundVolume (hc := hc) U u).val =
      gammaVolumeValue U.toGamma.toGammaRVObject (Section5.nativeRVGroundDomainEquiv (hc := hc) U u) :=
  gammaNativeRVGroundVolume_value U u

theorem gammaNativeRVGroundIso_gamma {U V : GammaObjectAt B Set.univ n}
    (e : GammaRVIso U.toGamma.toGammaRVObject V.toGamma.toGammaRVObject)
    (u : Section5.nativeRVGroundDomain (hc := hc) U) :
    Section5.nativeRVGroundDomainEquiv (hc := hc) V
      ((Section5.nativeRVGroundIso (hc := hc) (gammaIsoAtOfGamma e)).map u) =
      e.equiv (Section5.nativeRVGroundDomainEquiv (hc := hc) U u) := by
  apply Subtype.ext
  rfl

def gammaNativeRVRetainedForm (U : GammaObjectAt B Set.univ n)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) r))
    (ρ : Fin r → Fin (rvObjectArity U.object.obj))
    (hQ : ∀ u : Section5.nativeRVGroundDomain (hc := hc) U, u.val ∘ ρ ∈ Q.carrier)
    (ω : GammaGroundVolumeForm hc B Q) :=
  ω.comp ((gammaGroundRVSelectCoordinates ρ (Section5.nativeRVGroundDomain (hc := hc) U)).corestrict hQ)

def gammaNativeRetainedRVHom {U V : GammaObjectAt B Set.univ (n+1)}
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) r))
    (ρ : Fin r → Fin (rvObjectArity U.object.obj)) (τ : Fin r → Fin (rvObjectArity V.object.obj))
    (hU : ∀ u : Section5.nativeRVGroundDomain (hc := hc) U, u.val ∘ ρ ∈ Q.carrier)
    (hV : ∀ v : Section5.nativeRVGroundDomain (hc := hc) V, v.val ∘ τ ∈ Q.carrier)
    (ω : GammaGroundVolumeForm hc B Q)
    (e : GammaRVIso U.toGamma.toGammaRVObject V.toGamma.toGammaRVObject)
    (hProduct : ∀ u, (∏ i, Values.vrv (gammaVolumeValue V.toGamma.toGammaRVObject (e.equiv u) i)) =
      ∏ i, Values.vrv (gammaVolumeValue U.toGamma.toGammaRVObject u i))
    (hLabels : ∀ u, (e.equiv u).val ∘ τ = u.val ∘ ρ) :
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization U (gammaNativeRVRetainedForm U Q ρ hU ω))
      (gammaNativeMeasuredNormalization V (gammaNativeRVRetainedForm V Q τ hV ω)) := by
  apply gammaNativeRawMeasuredHom _ _ e
  · intro u
    rw [gammaNativeRVGroundVolume_gamma,gammaNativeRVGroundVolume_gamma,gammaNativeRVGroundIso_gamma]
    exact hProduct (Section5.nativeRVGroundDomainEquiv (hc := hc) U u)
  · intro u
    apply congrArg ω
    apply Subtype.ext
    exact (congrArg (fun q => q.val ∘ τ) (gammaNativeRVGroundIso_gamma e u)).trans
      (hLabels (Section5.nativeRVGroundDomainEquiv (hc := hc) U u))

end DiamondIntegral.Section3
