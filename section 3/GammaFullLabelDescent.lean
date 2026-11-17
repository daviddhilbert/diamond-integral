import «section 3».GammaGenericLiftDescent
import «section 3».GammaFiniteMapRealization
import IntegrationSection6.FiniteRVMorphisms

/-! A full original-Gamma VF bijection over a given RV-label bijection
descends the Gamma density equation on every RV label. Temporary real
realization is used only for the numerical polydisc identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open scoped BigOperators
namespace DiamondIntegral.Section3

inductive GammaLiftRealizationIndex
  | sourceVolume | targetVolume | rvMap | vfMap | sourceForm | targetForm
  deriving DecidableEq, Fintype

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaFullLabelDescent
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U V : GammaGroundMeasuredRVObject hc B k)
    (e : GammaGroundBijection U.underlying.domain V.underlying.domain)
    (f : GammaGroundBijection (gammaGroundObjectLift U.underlying) (gammaGroundObjectLift V.underlying))
    (hl : ∀ p, gammaGroundObjectLiftLabel V.underlying (f.map p) =
      e.map (gammaGroundObjectLiftLabel U.underlying p))
    (hm : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
      ∃ J : Section2.VF M, HasMixedVFJacobianAt f.map p J ∧
        gammaGroundMeasuredVFWeight (gammaGroundMeasuredObjectLift U) p =
          gammaGroundMeasuredVFWeight (gammaGroundMeasuredObjectLift V) (f.map p) * Values.vfValueHom J) :
    ∀ u, U.combinedWeight u = V.combinedWeight (e.map u) := by
  let P : GammaLiftRealizationIndex → Space LRV M
    | .sourceVolume | .rvMap | .sourceForm => rawRVSpace U.underlying.arity
    | .targetVolume | .targetForm => rawRVSpace V.underlying.arity
    | .vfMap => rawMixedSpace k U.underlying.arity
  let Q : GammaLiftRealizationIndex → Space LRV M
    | .sourceVolume | .targetVolume => rawRVSpace k
    | .rvMap => rawRVSpace V.underlying.arity
    | .vfMap => rawMixedSpace k V.underlying.arity
    | .sourceForm | .targetForm => volumeGammaSpace hc
  let A : ∀ i, GammaGroundDefSet hc B (P i)
    | .sourceVolume | .rvMap | .sourceForm => U.underlying.domain
    | .targetVolume | .targetForm => V.underlying.domain
    | .vfMap => gammaGroundObjectLift U.underlying
  let D : ∀ i, GammaGroundDefSet hc B (Q i)
    | .sourceVolume | .targetVolume => GammaGroundDefSet.univ hc B (rawRVSpace k)
    | .rvMap => V.underlying.domain
    | .vfMap => gammaGroundObjectLift V.underlying
    | .sourceForm | .targetForm => GammaGroundDefSet.univ hc B (volumeGammaSpace hc)
  let maps : ∀ i, GammaGroundMap (A i) (D i)
    | .sourceVolume => U.underlying.volume
    | .targetVolume => V.underlying.volume
    | .rvMap => e.map
    | .vfMap => f.map
    | .sourceForm => U.form
    | .targetForm => V.form
  obtain ⟨T,hBT,hsmall,hfield,hdata⟩ := gammaGroundMaps_realizeFinite P Q A D maps hκ.le hr
  let U₀ : SpecialTransformations.Section4.RVObject (M := M) T k := {
    arity := U.underlying.arity
    domain := ⟨U.underlying.domain.carrier,(hdata .sourceVolume).1⟩
    volume := ⟨U.underlying.volume.toFun,(relationDefinable_iff_product _).mpr (hdata .sourceVolume).2.2⟩ }
  let V₀ : SpecialTransformations.Section4.RVObject (M := M) T k := {
    arity := V.underlying.arity
    domain := ⟨V.underlying.domain.carrier,(hdata .targetVolume).1⟩
    volume := ⟨V.underlying.volume.toFun,(relationDefinable_iff_product _).mpr (hdata .targetVolume).2.2⟩ }
  let E : Map U₀.domain V₀.domain :=
    ⟨e.map.toFun,(relationDefinable_iff_product _).mpr (hdata .rvMap).2.2⟩
  let UF : RVFiniteObject (M := M) T k := ⟨U₀,U.underlying.finite⟩
  let VF : RVFiniteObject (M := M) T k := ⟨V₀,V.underlying.finite⟩
  have hweight (t : Fin k → CanonicalRV.RVSort M) (ht : ∀ i,(t i).val ≠ iRVZero) : rvWeight t = k := by
    simp [rvWeight, ht]
  let eF := IntegrationInACVF.Section6.FiniteRV.isoOfDefinableBijection UF VF E e.bijective (fun u =>
    (hweight (U₀.value u) (U.underlying.nonzero u)).trans
      (hweight (V₀.value (E u)) (V.underlying.nonzero (E u))).symm)
  let e₀ := (finiteVolumeProperty T k).ι.mapIso eF
  let F : Map (rvLift U₀) (rvLift V₀) :=
    ⟨f.map.toFun,(relationDefinable_iff_product _).mpr (hdata .vfMap).2.2⟩
  let ω : GammaVolumeForm hc U₀.domain :=
    ⟨U.form.toFun,(relationDefinable_iff_product _).mpr (hdata .sourceForm).2.2⟩
  let π : GammaVolumeForm hc V₀.domain :=
    ⟨V.form.toFun,(relationDefinable_iff_product _).mpr (hdata .targetForm).2.2⟩
  have hlabel (p : rvLift U₀) : e₀.hom.map.graph p.val.2 (F p).val.2 := by
    refine ⟨liftLabelMap U₀ p,rfl,?_⟩
    exact congrArg Subtype.val (hl p).symm
  have hmeasure (p : rvLift U₀) (hp : AlgebraicIndependent (vfParameterField T) p.val.1) :
      ∃ J : Section2.VF M, HasMixedVFJacobianAt F p J ∧
        (gammaFormValue ω (liftLabelMap U₀ p)).val =
          (gammaFormValue π (liftLabelMap V₀ (F p))).val * Values.vfValueHom J := by
    exact hm p (by rwa [hfield] at hp)
  have hdesc := gammaGenericLift_pointwise_descent hc hκ hs h00 hsmall e₀
    U.underlying.nonzero V.underlying.nonzero ω π F f.bijective hlabel hmeasure
  intro u
  have hu := hdesc u
  change gammaGroundFormValue U.form u = gammaGroundFormValue V.form (e.map u) *
    ((∏ i,Section2.rvFiniteValue (V.underlying.target (e.map u) i)) /
      ∏ i,Section2.rvFiniteValue (U.underlying.target u i)) at hu
  change gammaGroundFormValue U.form u * (∏ i,Section2.rvFiniteValue (U.underlying.target u i)) =
    gammaGroundFormValue V.form (e.map u) * (∏ i,Section2.rvFiniteValue (V.underlying.target (e.map u) i))
  rw [hu]
  simp [div_eq_mul_inv,mul_comm,mul_left_comm]

end DiamondIntegral.Section3
