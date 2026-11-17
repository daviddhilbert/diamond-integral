import «section 3».GammaGroundJacobianVFTransfer
import «section 3».GammaSpecialVFFamilyLifts
import «section 3».GammaSpecialFullMeasuredBijections
import «section 5».NativeVFBaseTransport
import «section 5».NativeSpecialBaseBridge

/-! Partial VF-base preparation has Jacobian one over the original base.
A lifted ordinary special chain supplies the Jacobian; the actual native
preparation has the same VF component. Real presentations may differ. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S SH : Set M} {p k l r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaPartialBasePointInput
    (H : DefSet (M := M) SH (p+k) r) (hH : GammaSetDefinable B (carrier H))
    (P : DefSet (M := M) S p 0) (hPG : GammaSetDefinable B (carrier P))
    (hP : ∀ q ∈ carrier H, (q.1 ∘ Fin.castAdd k,Fin.elim0) ∈ carrier P) :
    ∀ q : Section5.nativeGammaPointDomain (hc := hc) (carrier H) hH,
      ((Section5.nativeMixedCoordinateMap _ (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin r)) q).val ∈
        (Section5.nativeGammaPointDomain (hc := hc) (carrier P) hPG).carrier := by
  intro q
  change (q.val.1 ∘ Fin.castAdd k,q.val.2 ∘ Fin.elim0) ∈ carrier P
  exact (Prod.ext rfl (Subsingleton.elim _ _) :
    (q.val.1 ∘ Fin.castAdd k,Fin.elim0) = (q.val.1 ∘ Fin.castAdd k,q.val.2 ∘ Fin.elim0)) ▸ hP q.val q.property

theorem gammaPartialBase_jacobian_one
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {P : DefSet (M := M) S p 0} {D : DefSet (M := M) S p l}
    (T : SpecialBijection P D) (hT : GammaChainDefinable B T.chain)
    (H : DefSet (M := M) SH (p+k) r) (hH : GammaSetDefinable B (carrier H))
    (hP : ∀ q ∈ carrier H, (q.1 ∘ Fin.castAdd k,Fin.elim0) ∈ carrier P)
    (a : Section5.nativeGammaPointDomain (hc := hc) (carrier H) hH)
    (ha : AlgebraicIndependent (vfParameterField B.real) a.val.1) :
    HasMixedVFJacobianAt
      (Section5.nativeVFPrepareBaseBijection
        (Section5.nativeGammaPointDomain (hc := hc) (carrier H) hH)
        (Section5.nativeSpecialBaseBijection T hT)
        (gammaPartialBasePointInput (hc := hc) H hH P (GammaChainDefinable.source B T.chain hT) hP)).map a 1 := by
  let hSU : S ⊆ (Set.univ : Set M) := Set.subset_univ _
  let TU := T.extendBase hSU
  have hTU : GammaChainDefinable B TU.chain := GammaChainDefinable.extendBase B T.chain hSU hT
  let HU := extendBase H (Set.subset_univ SH)
  obtain ⟨L⟩ := gammaSpecialVFFamilyLift_exists TU hTU HU hH hP
  let F := gammaNativeSpecialBijection (hc := hc) L.special L.graph
  let A := Section5.nativeGammaPointDomain (hc := hc) (carrier H) hH
  let HP := gammaPartialBasePointInput (hc := hc) H hH P (GammaChainDefinable.source B T.chain hT) hP
  let N := Section5.nativeVFPrepareBaseBijection A (Section5.nativeSpecialBaseBijection T hT) HP
  have hVF (q : A) : (F.map q).val.1 = (N.map q).val.1 := by
    rw [gammaNativeSpecialBijection_apply]
    have hsq := congrArg Prod.fst (L.packed_square ⟨q.val,q.property⟩)
    have hBaseLift := T.chain.extendBase_apply hSU ⟨(q.val.1 ∘ Fin.castAdd k,Fin.elim0),hP q.val q.property⟩
    have hsq' := hsq.trans (congrArg (fun z => Fin.append z.1 (q.val.1 ∘ Fin.natAdd p)) hBaseLift)
    have hN := Section5.nativeVFPrepareBaseMap_value A (Section5.nativeSpecialBaseBijection T hT) HP q
    let b := Section5.nativeVFBaseParameterMap A (Section5.nativeGammaPointDomain (hc := hc) (carrier P)
      (GammaChainDefinable.source B T.chain hT)) HP q
    have hTval := Section5.nativeGammaPointBijection_apply
      (GammaChainDefinable.source B T.chain hT) (GammaChainDefinable.target B T.chain hT)
      (Section5.nativeSpecialBaseIso T hT) b
    have hb : (⟨b.val,b.property⟩ : P) = ⟨(q.val.1 ∘ Fin.castAdd k,Fin.elim0),hP q.val q.property⟩ :=
      Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))
    have hTval' := hTval.trans (congrArg (fun u : P => (T.toMap u).val) hb)
    exact hsq'.trans ((congrArg (fun z => Fin.append z.1 (q.val.1 ∘ Fin.natAdd p)) hTval').symm.trans
      (congrArg Prod.fst hN).symm)
  obtain ⟨D',hD,hdet⟩ := gammaSpecialChain_jacobian_one hc hκ hs hr hv L.special.chain L.graph
    ⟨a.val,a.property⟩ ha
  have hJF : HasMixedVFJacobianAt F.map a 1 := by
    obtain ⟨K,⟨ρ,hρ⟩,hK⟩ := hD
    refine ⟨K,⟨ρ,fun x hx => ?_⟩,by simpa only [hdet] using hK.hasJacobianAt⟩
    obtain ⟨hx,hv⟩ := hρ x hx
    refine ⟨hx,?_⟩
    rw [gammaNativeSpecialBijection_apply,gammaNativeSpecialBijection_apply]
    exact hv
  exact gammaGroundJacobian_transfer_VF hκ hs hr hv F.map N.map hVF a ha 1 hJF

end DiamondIntegral.Section3
