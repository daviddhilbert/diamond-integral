import «section 3».GammaSpecialJacobian
import «section 5».NativeAllVFBaseNormalForm

/-! Preparing the VF base of an arbitrary original-Gamma mixed domain
has actual Jacobian one on every independent point of that domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n r l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

include hκ hs hS hv in
theorem gammaPreparedBase_jacobian_one
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    {P : SpecialTransformations.Section5.DefSet (M := M) S n 0}
    {C : SpecialTransformations.Section5.DefSet (M := M) S n l}
    (T : SpecialTransformations.Section5.SpecialBijection P C)
    (hT : SpecialTransformations.Section5.GammaChainDefinable B T.chain)
    (hP : ∀ a : A,((Section5.nativeMixedCoordinateMap A (Fin.castAdd 0) (Fin.elim0 : Fin 0 → Fin r)) a).val ∈
      (Section5.nativeGammaPointDomain (hc := hc) (SpecialTransformations.Section5.carrier P)
        (SpecialTransformations.Section5.GammaChainDefinable.source B T.chain hT)).carrier)
    (a : A) (ha : AlgebraicIndependent (vfParameterField B.real) a.val.1) :
    HasMixedVFJacobianAt
      (Section5.nativeVFPrepareBaseBijection (k := 0) A (Section5.nativeSpecialBaseBijection T hT) hP).map a 1 := by
  let PΓ := Section5.nativeGammaPointDomain (hc := hc) (SpecialTransformations.Section5.carrier P)
    (SpecialTransformations.Section5.GammaChainDefinable.source B T.chain hT)
  let TΓ := Section5.nativeSpecialBaseBijection (hc := hc) T hT
  let f := Section5.nativeVFPrepareBaseBijection (k := 0) A TΓ hP
  let b := Section5.nativeVFBaseParameterMap (k := 0) A PΓ hP
  obtain ⟨L,hL,hdet⟩ := gammaSpecialChain_jacobian_one hc hκ hs hS hv T.chain hT (b a) ha
  obtain ⟨H,⟨ρ,hρ⟩,hHL⟩ := hL
  obtain ⟨D,K,⟨σ,hσ⟩,hKD⟩ := gammaGround_differentiable_of_independent hκ hs hS hv f.map a ha
  have hbase (u : A) : (f.map u).val.1 = (T.toMap (b u)).val.1 := by
    have hf := Section5.nativeVFPrepareAll_value A TΓ hP u
    have ht := Section5.nativeGammaPointBijection_apply
      (SpecialTransformations.Section5.GammaChainDefinable.source B T.chain hT)
      (SpecialTransformations.Section5.GammaChainDefinable.target B T.chain hT)
      (Section5.nativeSpecialBaseIso T hT) (b u)
    exact (congrArg Prod.fst hf).trans (congrArg Prod.fst ht)
  have hHK : Set.EqOn H K (vfBall a.val.1 (max ρ σ)) := by
    intro x hx
    obtain ⟨hp,hH⟩ := hρ x (vfBall_anti (le_max_left _ _) hx)
    obtain ⟨hq,hK⟩ := hσ x (vfBall_anti (le_max_right _ _) hx)
    let u : A := ⟨(x,a.val.2),hq⟩
    have he : (⟨(x,(b a).val.2),hp⟩ : P) = b u := by
      apply Subtype.ext
      exact Prod.ext rfl (Subsingleton.elim _ _)
    have hvf := congrArg Prod.fst hH
    rw [he] at hvf
    exact hvf.symm.trans ((hbase u).symm.trans (congrArg Prod.fst hK))
  have heq := (hHL.congr_on_vfBall hHK).unique hKD
  have hD : (LinearMap.toMatrix' D).det = 1 := heq ▸ hdet
  exact ⟨K,⟨σ,hσ⟩,by simpa only [hD] using hKD.hasJacobianAt⟩

end DiamondIntegral.Section3
