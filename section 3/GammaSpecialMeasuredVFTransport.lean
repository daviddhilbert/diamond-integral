import «section 3».GammaSpecialDensityTransport
import «section 3».GammaMeasuredArrowLift
import IntegrationSection6.FiniteRVGeometry

/-! Arbitrary original-ground special chains induce genuine measured VF
arrows with the transported Gamma form. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n m l : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S (n+1) m}
variable {D : SpecialTransformations.Section5.DefSet (M := M) S (n+1) l}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)

def gammaSpecialMeasuredSource (T : SpecialBijection A D) (hT : GammaChainDefinable B T.chain)
    (hfin : ∀ x, {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B
      (Section5.nativeGammaPointDomain (carrier A) (GammaChainDefinable.source B T.chain hT))) :
    GammaGroundMeasuredVFData hc B (n+1) :=
  ⟨m,Section5.nativeGammaPointDomain (carrier A) (GammaChainDefinable.source B T.chain hT),hfin,ω⟩

def gammaSpecialMeasuredTarget (T : SpecialBijection A D) (hT : GammaChainDefinable B T.chain)
    (hfin : ∀ x, {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B
      (Section5.nativeGammaPointDomain (carrier A) (GammaChainDefinable.source B T.chain hT))) :
    GammaGroundMeasuredVFData hc B (n+1) :=
  ⟨l,Section5.nativeGammaPointDomain (carrier D) (GammaChainDefinable.target B T.chain hT),
    finite_rv_fibres_of_gamma_bijection hκ hs hr T.toMap T.bijective
      (GammaChainDefinable.graph (gammaLogicInput B) T.chain hT) hfin,
    gammaSpecialTransportedForm T hT ω⟩

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaSpecialMeasuredVFHom
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : SpecialBijection A D) (hT : GammaChainDefinable B T.chain)
    (hfin : ∀ x, {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B
      (Section5.nativeGammaPointDomain (carrier A) (GammaChainDefinable.source B T.chain hT))) :
    GammaGroundMeasuredVFHom hκ hs hr hv (gammaSpecialMeasuredSource T hT hfin ω)
      (gammaSpecialMeasuredTarget hκ hs hr T hT hfin ω) := by
  let F := gammaNativeSpecialBijection (hc := hc) T hT
  apply gammaPositiveMeasuredHomOfBijection hκ hs hr hv F
  intro p hp
  let a : A := ⟨p.val,p.property⟩
  obtain ⟨L,hL,hdet⟩ := gammaSpecialChain_jacobian_one hc hκ hs hr hv T.chain hT a hp
  have hJ : HasMixedVFJacobianAt T.toMap a 1 := by
    obtain ⟨H,hH,hHL⟩ := hL
    refine ⟨H,hH,?_⟩
    simpa only [hdet] using hHL.hasJacobianAt
  have hF (q) : (F.map q).val = (T.toMap ⟨q.val,q.property⟩).val :=
    gammaNativeSpecialBijection_apply T hT q
  have hJF : HasMixedVFJacobianAt F.map p 1 := by
    obtain ⟨H,⟨ρ,hρ⟩,hH⟩ := hJ
    refine ⟨H,⟨ρ,fun x hx => ?_⟩,hH⟩
    obtain ⟨ha,hf⟩ := hρ x hx
    refine ⟨ha,?_⟩
    rw [hF,hF]
    exact hf
  refine ⟨1,hJF,?_⟩
  rw [map_one,mul_one]
  change (gammaGroundFormValue ω p).val =
    (gammaGroundFormValue ω (F.symm.map (F.map p))).val
  have hi : F.symm.map (F.map p) = p := F.map.inverse_apply F.bijective p
  exact congrArg (fun q => (gammaGroundFormValue ω q).val) hi.symm

end DiamondIntegral.Section3
