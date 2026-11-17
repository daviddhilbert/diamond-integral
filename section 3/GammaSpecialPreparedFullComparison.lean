import «section 3».GammaSpecialFullMeasuredBijections
import «section 3».GammaNativePullbackFullComparison

/-! A density-coherent special preparation compares the original full
measured VF object with the actual full-key measured RV lift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) m}
variable {C : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) l}
variable (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain)
variable (hCP : IsRVPullback (carrier C))
variable (hCF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject C)))
variable (hfin : ∀ x, {r | (x,r) ∈ carrier A}.Finite)
variable (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) (GammaChainDefinable.source B T.chain hT)))
variable (π : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain
  (gammaPullbackAt (Set.subset_univ _) C (GammaChainDefinable.target B T.chain hT) hCF)))
variable (hπ : ∀ p, π (gammaNativePullbackKeyMap C (GammaChainDefinable.target B T.chain hT) hCF
  ((gammaNativeSpecialBijection T hT).map p)) = ω p)

def gammaSpecialPreparedFullMeasured : GammaFullMeasuredBijection
    (gammaSpecialMeasuredSource T hT hfin ω)
    (gammaNativeMeasuredLift (gammaPullbackAt (Set.subset_univ _) C (GammaChainDefinable.target B T.chain hT) hCF) π) := by
  let F := gammaSpecialFullMeasuredBijection hκ hs hr hv T hT hfin ω
  let FT := gammaNativeSpecialBijection (hc := hc) T hT
  let hC := GammaChainDefinable.target B T.chain hT
  let hfinC := finite_rv_fibres_of_gamma_bijection hκ hs hr T.toMap T.bijective
    (GammaChainDefinable.graph (gammaLogicInput B) T.chain hT) hfin
  have Hπ : ∀ q, π (gammaNativePullbackKeyMap C hC hCF q) = gammaSpecialTransportedForm T hT ω q := by
    intro q
    have H := hπ (FT.symm.map q)
    have he : FT.map (FT.symm.map q) = q := FT.map.apply_inverse FT.bijective q
    rw [he] at H
    exact H
  let G := gammaNativePullbackFullMeasured C hC hCP hCF hκ hs hr hv hfinC
    (gammaSpecialTransportedForm T hT ω) π Hπ
  exact F.comp hκ hs hr hv G

theorem gammaSpecialPreparedFullMeasured_label
    (p : Section5.nativeGammaPointDomain (hc := hc) (carrier A) (GammaChainDefinable.source B T.chain hT)) :
    gammaNativeLiftLabel (gammaPullbackAt (Set.subset_univ _) C (GammaChainDefinable.target B T.chain hT) hCF)
      ((gammaSpecialPreparedFullMeasured hκ hs hr hv T hT hCP hCF hfin ω π hπ).map.map p) =
      gammaNativePullbackKeyMap C (GammaChainDefinable.target B T.chain hT) hCF
        ((gammaNativeSpecialBijection T hT).map p) := by
  exact gammaNativePullbackLiftBijection_label C _ hCP hCF ((gammaNativeSpecialBijection T hT).map p)

end DiamondIntegral.Section3
