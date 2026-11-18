import «section 3».GammaSpecialFamilyKeys
import «section 3».GammaNativePullbackForms
import «section 3».GammaIndexedOriginalLabels

/-! The actual extended special preparation and the existing finite-row
indexed presentation have a bijective original-Gamma RV coordinate map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p l a : ℕ}
variable {X : SpecialTransformations.Section5.DefSet (M := M) Set.univ p 0}
variable {Z : SpecialTransformations.Section5.DefSet (M := M) Set.univ p l}
variable {H : SpecialTransformations.Section5.DefSet (M := M) Set.univ p a}
variable {T : SpecialBijection X Z}
variable {hHX : ∀ q ∈ carrier H, (q.1,Fin.elim0) ∈ carrier X}
variable (L : GammaSpecialFamilyLift (B := B) T H hHX)
variable (F : GammaFiniteRVSchema B p a 0) (G : GammaFiniteRVSchema B (p+l) a 0 (fun _ => .rv))
variable (hSource : carrier H = vfSchemaSource (carrier X) F)
variable (hRows : ∀ q : Z, GammaSchemaRowAgreement F (rawVFParameter (T.inverseMap q).val) G (rawPreparedKey q.val))
variable (BP : PreparedIndexPresentation B Z) (P : G.IndexedPresentation BP)
variable (hKF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject L.target)))

def gammaSpecialFamilyRVMap :
    GammaGroundMap (Section5.nativeRVGroundDomain (hc := hc)
      (gammaPullbackAt (Set.subset_univ _) L.target (GammaChainDefinable.target B L.special.chain L.graph) hKF))
      (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :=
  (gammaGroundRVSelectCoordinates (gammaFamilyKeyIndices L.projection (gammaChainOldLabelIndex L.special.chain))
    (Section5.nativeRVGroundDomain (hc := hc)
      (gammaPullbackAt (Set.subset_univ _) L.target (GammaChainDefinable.target B L.special.chain L.graph) hKF))).corestrict (fun u => by
        obtain ⟨q,hq⟩ := gammaNativePullbackKeyMap_surjective L.target
          (GammaChainDefinable.target B L.special.chain L.graph) hKF u
        have hkey : u.val = (flatKey q.val).2 := (congrArg Subtype.val hq).symm
        apply (Section5.nativeRVGroundDomain_carrier (gammaUniversalObject P.toGamma)).ge
        apply P.domain_eq.ge
        change gammaFamilyKeyCode L.projection (gammaChainOldLabelIndex L.special.chain) u.val ∈ _
        rw [hkey]
        exact (gammaSpecialFamilyLift_key_image L F G hSource hRows).le ⟨_,⟨⟨q.val,q.property⟩,rfl⟩,rfl⟩)

theorem gammaSpecialFamilyRVMap_val
    (u : Section5.nativeRVGroundDomain (hc := hc)
      (gammaPullbackAt (Set.subset_univ _) L.target (GammaChainDefinable.target B L.special.chain L.graph) hKF)) :
    (gammaSpecialFamilyRVMap L F G hSource hRows BP P hKF u).val =
      gammaFamilyKeyCode L.projection (gammaChainOldLabelIndex L.special.chain) u.val := rfl

theorem gammaSpecialFamilyRVMap_bijective :
    Function.Bijective (gammaSpecialFamilyRVMap (hc := hc) L F G hSource hRows BP P hKF) := by
  constructor
  · intro u v huv
    exact Subtype.ext (gammaFamilyKeyCode_injective L.projection (gammaChainOldLabelIndex L.special.chain)
      L.cover (congrArg Subtype.val huv))
  · intro v
    have hv := P.domain_eq.le (Section5.nativeRVGroundDomainEquiv (gammaUniversalObject P.toGamma) v).property
    obtain ⟨_,⟨q,rfl⟩,hq⟩ := (gammaSpecialFamilyLift_key_image L F G hSource hRows).ge hv
    let u := gammaNativePullbackKeyMap (hc := hc) L.target (GammaChainDefinable.target B L.special.chain L.graph) hKF
      ⟨q.val,q.property⟩
    refine ⟨u,Subtype.ext ?_⟩
    exact hq

def gammaSpecialFamilyRVBijection :=
  GammaGroundBijection.mk (gammaSpecialFamilyRVMap (hc := hc) L F G hSource hRows BP P hKF)
    (gammaSpecialFamilyRVMap_bijective L F G hSource hRows BP P hKF)

end DiamondIntegral.Section3
