import «section 3».GammaPartialBaseJacobian
import «section 3».GammaHeadMeasuredFibres

/-! Actual preparation of a VF prefix transports a complete Gamma form
and defines a full measured bijection. All parameters remain in the
original real/Gamma base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S SH : Set M} {p k l r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
variable {P : DefSet (M := M) S p 0} {D : DefSet (M := M) S p l}
variable (T : SpecialBijection P D) (hT : GammaChainDefinable B T.chain)
variable (H : DefSet (M := M) SH (p+k) r) (hH : GammaSetDefinable B (carrier H))
variable (hP : ∀ a : Section5.nativeGammaPointDomain (hc := hc) (carrier H) hH,
  ((Section5.nativeMixedCoordinateMap _ (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin r)) a).val ∈
    (Section5.nativeGammaPointDomain (hc := hc) (carrier P) (GammaChainDefinable.source B T.chain hT)).carrier)
variable (hfin : ∀ x, {t | (x,t) ∈ carrier H}.Finite)
variable (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (hc := hc) (carrier H) hH))

def gammaPartialBasePreparedData : GammaGroundMeasuredVFData hc B (p+k) :=
  let A := Section5.nativeGammaPointDomain (hc := hc) (carrier H) hH
  let F := Section5.nativeVFPrepareBaseBijection A (Section5.nativeSpecialBaseBijection T hT) hP
  ⟨l+r, (Section5.nativeVFPrepareBaseMap A (Section5.nativeSpecialBaseBijection T hT) hP).image,
    Section5.nativeVFPrepareBaseMap_finite hκ hs h00 hr A (Section5.nativeSpecialBaseBijection T hT) hP hfin,
    ω.comp F.symm.map⟩

def gammaPartialBaseFullMeasured
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    GammaFullMeasuredBijection (gammaPointMeasuredData H hH hfin ω)
      (gammaPartialBasePreparedData hκ hs h00 hr T hT H hH hP hfin ω) := by
  let A := Section5.nativeGammaPointDomain (hc := hc) (carrier H) hH
  let F := Section5.nativeVFPrepareBaseBijection A (Section5.nativeSpecialBaseBijection T hT) hP
  refine ⟨F,?_⟩
  intro a ha
  have hP' : ∀ q ∈ carrier H, (q.1 ∘ Fin.castAdd k,Fin.elim0) ∈ carrier P := by
    intro q hq
    have h := hP ⟨q,hq⟩
    change (q.1 ∘ Fin.castAdd k,q.2 ∘ Fin.elim0) ∈ carrier P at h
    exact (Prod.ext rfl (Subsingleton.elim _ _) :
      (q.1 ∘ Fin.castAdd k,q.2 ∘ Fin.elim0) = (q.1 ∘ Fin.castAdd k,Fin.elim0)) ▸ h
  have hJ : HasMixedVFJacobianAt F.map a 1 :=
    gammaPartialBase_jacobian_one hκ hs hr hv T hT H hH hP' a ha
  refine ⟨1,hJ,?_⟩
  rw [map_one,mul_one]
  change (gammaGroundFormValue ω a).val = (gammaGroundFormValue ω (F.symm.map (F.map a))).val
  exact congrArg (fun q => (gammaGroundFormValue ω q).val) (F.map.inverse_apply F.bijective a).symm

end DiamondIntegral.Section3
