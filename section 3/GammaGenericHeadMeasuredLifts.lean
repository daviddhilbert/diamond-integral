import «section 3».GammaHeadLiftForms
import «section 3».GammaTracedHeadMeasuredFibres
import «section 3».GammaNativeAlmostEverywhereJacobians
import «section 3».GammaTracedHeadFibreJacobians

/-! A certified head preparation and its canonical lift form a full
measured comparison with the original retained Gamma density. The proof
uses the native trace compiler, with no change of the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {U : DefSet (M := M) Set.univ (n+1) a}

theorem gammaGenericHead_full_measured_lift
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : HeadPreparation U)
    (hU : GammaSetDefinable B (carrier U))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hJac : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
      HasMixedVFJacobianAt (Section5.nativeGammaPointBijection (hc := hc) hU
        (gamma_coordinateCanonicalImage T.target hTarget 0)
        (⟨Equiv.ofBijective T.liftMap T.liftMap_bijective,
          gamma_composition_graph T.map (coordinateCanonicalBijection T.target 0) hT
            (gamma_coordinateCanonical_graph T.target hTarget 0)⟩ : GammaIso B (carrier U) (carrier T.liftSet))).map p 1)
    (hfin : ∀ x, {r | (x,r) ∈ carrier U}.Finite)
    (Q : GammaGroundDefSet hc B (SpecialTransformations.Section4.rawRVSpace (M := M) a))
    (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    let Ω := gammaPointRetainedForm U hU Q id (fun u => hLabels u) ω
    let η := gammaHeadLiftForm T hTarget Q hLabels ω
    ∃ hfinH : ∀ x, {r | (x,r) ∈ carrier T.liftSet}.Finite,
    ∃ F : GammaFullMeasuredBijection
      (gammaPointMeasuredData (hc := hc) U hU hfin Ω)
      (gammaPointMeasuredData T.liftSet (gamma_coordinateCanonicalImage T.target hTarget 0) hfinH η),
      ∀ p, (F.map.map p).val = (T.liftMap ⟨p.val,p.property⟩).val := by
  intro Ω η
  let hH := gamma_coordinateCanonicalImage T.target hTarget 0
  let hGraph := gamma_composition_graph T.map (coordinateCanonicalBijection T.target 0) hT
    (gamma_coordinateCanonical_graph T.target hTarget 0)
  let e : GammaIso B (carrier U) (carrier T.liftSet) :=
    ⟨Equiv.ofBijective T.liftMap T.liftMap_bijective,hGraph⟩
  have hfinH := finite_rv_fibres_of_gamma_bijection hκ hs hr T.liftMap T.liftMap_bijective hGraph hfin
  let g := Section5.nativeGammaPointBijection (hc := hc) hU hH e
  have hg (p : Section5.nativeGammaPointDomain (hc := hc) (carrier U) hU) :
      (g.map p).val = (T.liftMap ⟨p.val,p.property⟩).val :=
    Section5.nativeGammaPointBijection_apply hU hH e p
  let F : GammaFullMeasuredBijection (gammaPointMeasuredData U hU hfin Ω)
      (gammaPointMeasuredData T.liftSet hH hfinH η) :=
    gammaFullMeasuredOfJacobianOne g hJac (by
      intro p
      have he : g.map p = ⟨(T.liftMap ⟨p.val,p.property⟩).val,(T.liftMap ⟨p.val,p.property⟩).property⟩ :=
        Subtype.ext (hg p)
      change (gammaGroundFormValue Ω p).val = (gammaGroundFormValue η (g.map p)).val
      rw [he]
      exact (congrArg (fun q => (cast (gammaCarrier hc) q.val).val)
        (gammaHeadLiftForm_apply T hTarget Q hLabels ω ⟨p.val,p.property⟩)).symm)
  exact ⟨hfinH,F,hg⟩

theorem gammaGenericHead_full_measured_fibres
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : HeadPreparation U)
    (hU : GammaSetDefinable B (carrier U))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hJac : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
      HasMixedVFJacobianAt (Section5.nativeGammaPointBijection (hc := hc) hU
        (gamma_coordinateCanonicalImage T.target hTarget 0)
        (⟨Equiv.ofBijective T.liftMap T.liftMap_bijective,
          gamma_composition_graph T.map (coordinateCanonicalBijection T.target 0) hT
            (gamma_coordinateCanonical_graph T.target hTarget 0)⟩ : GammaIso B (carrier U) (carrier T.liftSet))).map p 1)
    (hfin : ∀ x, {r | (x,r) ∈ carrier U}.Finite)
    (Q : GammaGroundDefSet hc B (SpecialTransformations.Section4.rawRVSpace (M := M) a))
    (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    let Ω := gammaPointRetainedForm U hU Q id (fun u => hLabels u) ω
    let η := gammaHeadLiftForm T hTarget Q hLabels ω
    ∃ hfinH : ∀ x, {r | (x,r) ∈ carrier T.liftSet}.Finite,
      ∀ x : Fin n → VF (M := M), AlgebraicIndependent (vfParameterField B.real) x →
        Nonempty (GammaFullMeasuredBijection
          (gammaHeadMeasuredFibre U hU hfin Ω x)
          (gammaHeadMeasuredFibre T.liftSet (gamma_coordinateCanonicalImage T.target hTarget 0) hfinH η x)) := by
  intro Ω η
  obtain ⟨hfinH,F,hF⟩ := gammaGenericHead_full_measured_lift (hc := hc) hκ hs h00 hr hv T hU hTarget hT hJac hfin Q hLabels ω
  have hGraph : GammaGraphDefinable B (pointMapGraph T.liftMap) :=
    gamma_composition_graph T.map (coordinateCanonicalBijection T.target 0)
      hT (gamma_coordinateCanonical_graph T.target hTarget 0)
  have hUnary : UnaryRelative T.liftMap 0 := by
    intro u j hj
    exact specialRelative_unaryRelative T.special u j hj
  refine ⟨hfinH,fun x hx => ⟨?_⟩⟩
  exact gammaFullMeasuredHeadFibre hU (gamma_coordinateCanonicalImage T.target hTarget 0)
    hfin hfinH Ω η F T.liftMap T.liftMap_bijective hGraph hF hUnary x hx

end DiamondIntegral.Section3
