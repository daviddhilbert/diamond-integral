import «section 3».GammaWeightedLiftClosureDescent
import «section 3».GammaMeasuredHomLift
import «section 3».GammaGroundMeasuredVFScissors
import «section 5».Completed18LocalLift

/-! Forward measured lifting over the original real/Gamma ground. All
structural labels and the exact Gamma density are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace
  SpecialTransformations.Section4.rawRVSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section9
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hS : Cardinal.mk B.real < κ)
variable (hγ : Cardinal.mk B.gamma < κ) (hB : VFGammaGeneratedBase (closureBase B))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

include hκ hs h00 hS hγ hB hv in
theorem gammaMeasuredHom_lift_bijection_closure
    {U V : GammaGroundMeasuredRVObject hc B k} (e : GammaGroundMeasuredRVHom U V) :
    ∃ f : GammaGroundBijection (gammaGroundObjectLift U.underlying) (gammaGroundObjectLift V.underlying),
      (∀ p, gammaGroundObjectLiftLabel V.underlying (f.map p) =
        e.bijection.map (gammaGroundObjectLiftLabel U.underlying p)) ∧
      ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
        ∃ J : Section2.VF M, HasMixedVFJacobianAt f.map p J ∧
          gammaGroundMeasuredVFWeight (gammaGroundMeasuredObjectLift U) p =
            gammaGroundMeasuredVFWeight (gammaGroundMeasuredObjectLift V) (f.map p) * Values.vfValueHom J := by
  let NU := Section5.groundRVAt U.underlying
  let NV := Section5.groundRVAt V.underlying
  let ne := (Section5.groundRVAtIso e.bijection).toGamma
  have hnU (u : SpecialTransformations.Section5.rvObjectDomain NU.object.obj) (i : Fin k) :
      (SpecialTransformations.Section7.gammaVolumeValue NU.toGamma.toGammaRVObject u i).val ≠ iRVZero := by
    change ((SpecialTransformations.Section5.rvObjectVolume NU.object.obj u).val i).val ≠ _
    rw [Section5.groundRVAt_volume_eq]
    exact U.underlying.nonzero _ i
  have hnV (u : SpecialTransformations.Section5.rvObjectDomain NV.object.obj) (i : Fin k) :
      (SpecialTransformations.Section7.gammaVolumeValue NV.toGamma.toGammaRVObject u i).val ≠ iRVZero := by
    change ((SpecialTransformations.Section5.rvObjectVolume NV.object.obj u).val i).val ≠ _
    rw [Section5.groundRVAt_volume_eq]
    exact V.underlying.nonzero _ i
  obtain ⟨nf,hlabels,hjac⟩ := gammaWeightedLift_closure_descent hc hκ hs h00 hS hγ hB Valued.v hv
    (Set.subset_univ _) (Set.subset_univ _) ne hnU hnV
  let P := GammaGroundBijection.ofCarrierEq (hc := hc) (ground := B)
    (A := gammaGroundObjectLift U.underlying)
    (B := Section5.nativeGammaPointDomain NU.toGamma.toGammaRVObject.lift NU.toGamma.toGammaRVObject.lift_definable)
    (Section5.groundRVAt_lift_domain U.underlying).symm
  let Q := GammaGroundBijection.ofCarrierEq (hc := hc) (ground := B)
    (A := Section5.nativeGammaPointDomain NV.toGamma.toGammaRVObject.lift NV.toGamma.toGammaRVObject.lift_definable)
    (B := gammaGroundObjectLift V.underlying) (Section5.groundRVAt_lift_domain V.underlying)
  let F := Section5.nativeGammaPointBijection (hc := hc) NU.toGamma.toGammaRVObject.lift_definable NV.toGamma.toGammaRVObject.lift_definable nf
  let f := Q.comp (F.comp P)
  have hf (p : gammaGroundObjectLift U.underlying) :
      (f.map p).val = (nf.equiv ⟨p.val,(Section5.groundRVAt_lift_domain U.underlying).symm ▸ p.property⟩).val :=
    Section5.nativeGammaPointBijection_apply _ _ nf (P.map p)
  have hl (p : gammaGroundObjectLift U.underlying) :
      gammaGroundObjectLiftLabel V.underlying (f.map p) =
        e.bijection.map (gammaGroundObjectLiftLabel U.underlying p) := by
    obtain ⟨u,hu,hv'⟩ := hlabels (P.map p)
    have he : (Section5.groundRVAtDomainEquiv U.underlying).symm u =
        gammaGroundObjectLiftLabel U.underlying p := Subtype.ext hu
    apply Subtype.ext
    rw [gammaGroundObjectLiftLabel_value,hf]
    exact hv'.symm.trans (congrArg (fun a : U.underlying.domain => (e.bijection.map a).val) he)
  refine ⟨f,hl,fun p hp => ?_⟩
  obtain ⟨J,hJ,hvJ⟩ := hjac (P.map p) hp
  have hJF : HasMixedVFJacobianAt f.map p J := by
    obtain ⟨H,⟨ρ,hρ⟩,hHJ⟩ := hJ
    refine ⟨H,⟨ρ,fun x hx => ?_⟩,hHJ⟩
    obtain ⟨hm,ho⟩ := hρ x hx
    have hm' : (x,p.val.2) ∈ (gammaGroundObjectLift U.underlying).carrier := by
      exact (Section5.groundRVAt_lift_domain U.underlying).le hm
    refine ⟨hm',?_⟩
    rw [hf,hf]
    exact ho
  have hval : Values.vfValueHom J =
      Values.vfValueHom ((∏ i,(f.map p).val.1 i) / ∏ i,p.val.1 i) := by
    apply (Section2.vfValue_eq_iff Valued.v hv _ _).mpr
    simpa only [map_div₀,map_prod,hf,P,GammaGroundBijection.ofCarrierEq,GammaGroundMap.inclusion] using hvJ
  let u := gammaGroundObjectLiftLabel U.underlying p
  let v := gammaGroundObjectLiftLabel V.underlying (f.map p)
  have hb := congrArg (fun γ : Values.Gamma (M := M) => γ.val) (e.preserves u)
  change (U.combinedWeight u).val = (V.combinedWeight (e.bijection.map u)).val at hb
  rw [← hl p] at hb
  change (gammaGroundFormValue U.form u).val *
      (∏ i,Section2.rvFiniteValue (U.underlying.target u i)).val =
    (gammaGroundFormValue V.form v).val *
      (∏ i,Section2.rvFiniteValue (V.underlying.target v i)).val at hb
  rw [gammaMeasuredLift_volume_value,gammaMeasuredLift_volume_value] at hb
  have hpn : Values.vfValueHom (∏ i,p.val.1 i) ≠ 0 := by
    rw [← gammaMeasuredLift_volume_value U.underlying p]
    rw [← Values.infinity_eq_zero]
    exact (∏ i, Section2.rvFiniteValue (U.underlying.target (gammaGroundObjectLiftLabel U.underlying p) i)).property
  refine ⟨J,hJF,?_⟩
  change (gammaGroundFormValue U.form u).val = (gammaGroundFormValue V.form v).val * Values.vfValueHom J
  rw [hval,map_div₀,← mul_div_assoc,← hb,mul_div_cancel_right₀ _ hpn]

end DiamondIntegral.Section3
