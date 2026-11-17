import «section 3».GammaMeasuredUnaryChainEndpoints
import «section 3».GammaFullMeasuredRestrictions
import IntegrationSection5.UnaryPartition

/-! The existing finite unary partition upgrades to actual Gamma
measured chains on every piece. Both original endpoint forms and the
given bijection are retained over the original, unrestricted base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaFullMeasured_unary_partition
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ1 : 1 < δ)
    {U V : GammaGroundMeasuredVFData hc B (n+1)} (F : GammaFullMeasuredBijection U V) :
    ∃ Q : GammaUnaryPartition (gammaGroundPointIso F.map),
      ∀ A (hA : A ∈ Q.pieces),
      ∃ D : Set (Point (M := M) (n+1) V.arity),
      ∃ hD : GammaSetDefinable B D, ∃ hDV : D ⊆ V.domain.carrier,
      ∃ H : GammaMeasuredUnaryChain
        (U.restrict (Section5.nativeGammaPointDomain A (Q.definable A hA)) (Q.subset A hA))
        (V.restrict (Section5.nativeGammaPointDomain D hD) hDV),
        ∀ p, ((H.fullMap hκ hs hr hv).map.map p).val =
          (F.map.map ⟨p.val,Q.subset A hA p.property⟩).val := by
  obtain ⟨Q,_⟩ := lemma_5_6_iso hκ hs h00 hr δ hδ1 (gammaGroundPointIso F.map)
  refine ⟨Q,?_⟩
  intro A hA
  obtain ⟨D,T,hT⟩ := Q.factors A hA
  have hAD := Q.definable A hA
  have hD := T.toIso.target_definable (gammaLogicInput B)
  have hDV : D ⊆ V.domain.carrier := by
    intro q hq
    obtain ⟨p,hp⟩ := T.toIso.equiv.surjective ⟨q,hq⟩
    have he := (congrArg Subtype.val hp).symm.trans (hT p)
    have hm : ((gammaGroundPointIso F.map).equiv ⟨p.val,Q.subset A hA p.property⟩).val ∈ V.domain.carrier :=
      ((gammaGroundPointIso F.map).equiv ⟨p.val,Q.subset A hA p.property⟩).property
    exact Eq.mpr (congrArg (fun z : Point (M := M) (n+1) V.arity => z ∈ V.domain.carrier) he) hm
  let A₀ := Section5.nativeGammaPointDomain (hc := hc) A hAD
  let D₀ := Section5.nativeGammaPointDomain (hc := hc) D hD
  let g := Section5.nativeGammaPointBijection (hc := hc) hAD hD T.toIso
  have hMap (p : A₀) : (g.map p).val = (F.map.map ⟨p.val,Q.subset A hA p.property⟩).val :=
    (Section5.nativeGammaPointBijection_apply hAD hD T.toIso p).trans (hT ⟨p.val,p.property⟩)
  let R := gammaFullMeasuredRestriction hκ hs hr hv F A₀ (Q.subset A hA) D₀ hDV g hMap
  obtain ⟨H,hH⟩ := gammaMeasuredUnaryChain_with_endpoints hκ hs hr hv R T
    (fun p => (Section5.nativeGammaPointBijection_apply hAD hD T.toIso p).symm)
  exact ⟨D,hD,hDV,H,fun p => (hH p).trans (hMap p)⟩

end DiamondIntegral.Section3
