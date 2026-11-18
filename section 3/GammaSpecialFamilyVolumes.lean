import «section 3».GammaSpecialFamilyRVIsomorphisms
import «section 3».GammaIndexedEssentialLabels
import «section 3».GammaNativeMeasuredGroundIsomorphisms

/-! The actual indexed-family coordinate map preserves the entire
structural volume tuple. The existing measured descent adapter therefore
applies to arbitrary Gamma forms preserved by that same map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n l a : ℕ}

theorem gammaNativePullbackVolume
    (K : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) l)
    (hK : GammaSetDefinable B (carrier K))
    (hKF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject K)))
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaPullbackAt (Set.subset_univ _) K hK hKF)) :
    (Section5.nativeRVGroundVolume (gammaPullbackAt (Set.subset_univ _) K hK hKF) u).val =
      u.val ∘ Fin.castAdd l := by
  rw [gammaNativeRVGroundVolume_value]
  rfl

variable {X : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) 0}
variable {Z : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) l}
variable {H : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) a}
variable {T : SpecialBijection X Z}
variable {hHX : ∀ q ∈ carrier H, (q.1,Fin.elim0) ∈ carrier X}
variable (L : GammaSpecialFamilyLift (B := B) T H hHX)
variable (F : GammaFiniteRVSchema B (n+1) a 0) (G : GammaFiniteRVSchema B ((n+1)+l) a 0 (fun _ => .rv))
variable (hSource : carrier H = vfSchemaSource (carrier X) F)
variable (hRows : ∀ q : Z, GammaSchemaRowAgreement F (rawVFParameter (T.inverseMap q).val) G (rawPreparedKey q.val))
variable (BP : PreparedIndexPresentation B Z) (P : G.IndexedPresentation BP)
variable (hKF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject L.target)))

theorem gammaSpecialFamilyRVBijection_volume
    (u : Section5.nativeRVGroundDomain (hc := hc)
      (gammaPullbackAt (Set.subset_univ _) L.target (GammaChainDefinable.target B L.special.chain L.graph) hKF)) :
    (Section5.nativeRVGroundVolume
      (gammaPullbackAt (Set.subset_univ _) L.target (GammaChainDefinable.target B L.special.chain L.graph) hKF) u).val =
    (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma)
      ((gammaSpecialFamilyRVBijection L F G hSource hRows BP P hKF).map u)).val := by
  let v := (gammaSpecialFamilyRVBijection (hc := hc) L F G hSource hRows BP P hKF).map u
  have hv := P.domain_eq.le (Section5.nativeRVGroundDomainEquiv (gammaUniversalObject P.toGamma) v).property
  have h1 := gammaIndexed_groundVolume BP G P v
  have h2 := PreparedIndexPresentation.totalVolume_eq Z BP (v.val ∘ Fin.castAdd a) hv.1
  have h3 : v.val ∘ Fin.castAdd a ∘ Fin.castAdd l = u.val ∘ Fin.castAdd L.arity :=
    gammaFamilyKeyCode_prefix L.projection (gammaChainOldLabelIndex L.special.chain) u.val
  exact (gammaNativePullbackVolume L.target (GammaChainDefinable.target B L.special.chain L.graph) hKF u).trans
    ((h1.trans (h2.trans h3)).symm)

def gammaSpecialFamilyMeasuredHom
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain
      (gammaPullbackAt (Set.subset_univ _) L.target (GammaChainDefinable.target B L.special.chain L.graph) hKF)))
    (π : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (gammaUniversalObject P.toGamma)))
    (hω : ∀ u, gammaGroundFormValue ω u = gammaGroundFormValue π
      ((gammaSpecialFamilyRVBijection L F G hSource hRows BP P hKF).map u)) :
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization
        (gammaPullbackAt (Set.subset_univ _) L.target (GammaChainDefinable.target B L.special.chain L.graph) hKF) ω)
      (gammaNativeMeasuredNormalization (gammaUniversalObject P.toGamma) π) :=
  gammaNativeMeasuredGroundHom _ _ ω π (gammaSpecialFamilyRVBijection L F G hSource hRows BP P hKF)
    (gammaSpecialFamilyRVBijection_volume L F G hSource hRows BP P hKF) hω

end DiamondIntegral.Section3
