import «section 3».GammaGenericHeadMeasuredLifts
import «section 3».GammaHeadRawRowMeasuredBridge
import «section 3».GammaTracedHeadMeasuredFibres

/-! A relatively unary full measured map compares the raw unary RV rows
of certified head preparations, with the actual retained Gamma forms.
Only the frozen VF tail is named in each row. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a b : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {U : DefSet (M := M) Set.univ (n+1) a} {V : DefSet (M := M) Set.univ (n+1) b}

theorem gammaRelativeGenericHead_full_measured_row_map
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ y z : Section2.VF M, VFValued.predV y z ↔ Valued.v y ≤ Valued.v z)
    (T : HeadPreparation U) (E : HeadPreparation V)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hTargetT : GammaSetDefinable B (carrier T.target)) (hTargetE : GammaSetDefinable B (carrier E.target))
    (hMapT : GammaGraphDefinable B (pointMapGraph T.map)) (hMapE : GammaGraphDefinable B (pointMapGraph E.map))
    (hJacT : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
      HasMixedVFJacobianAt (Section5.nativeGammaPointBijection (hc := hc) hU
        (gamma_coordinateCanonicalImage T.target hTargetT 0)
        (⟨Equiv.ofBijective T.liftMap T.liftMap_bijective,
          gamma_composition_graph T.map (coordinateCanonicalBijection T.target 0) hMapT
            (gamma_coordinateCanonical_graph T.target hTargetT 0)⟩ : GammaIso B (carrier U) (carrier T.liftSet))).map p 1)
    (hJacE : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
      HasMixedVFJacobianAt (Section5.nativeGammaPointBijection (hc := hc) hV
        (gamma_coordinateCanonicalImage E.target hTargetE 0)
        (⟨Equiv.ofBijective E.liftMap E.liftMap_bijective,
          gamma_composition_graph E.map (coordinateCanonicalBijection E.target 0) hMapE
            (gamma_coordinateCanonical_graph E.target hTargetE 0)⟩ : GammaIso B (carrier V) (carrier E.liftSet))).map p 1)
    (hfinU : ∀ x, {r | (x,r) ∈ carrier U}.Finite) (hfinV : ∀ x, {r | (x,r) ∈ carrier V}.Finite)
    (A : GammaGroundDefSet hc B (SpecialTransformations.Section4.rawRVSpace (M := M) a))
    (D : GammaGroundDefSet hc B (SpecialTransformations.Section4.rawRVSpace (M := M) b))
    (hLabelsU : ∀ u : U, u.val.2 ∈ A.carrier) (hLabelsV : ∀ v : V, v.val.2 ∈ D.carrier)
    (ω : GammaGroundVolumeForm hc B A) (η : GammaGroundVolumeForm hc B D)
    (F : GammaFullMeasuredBijection
      (gammaPointMeasuredData U hU hfinU (gammaPointRetainedForm U hU A id (fun u => hLabelsU u) ω))
      (gammaPointMeasuredData V hV hfinV (gammaPointRetainedForm V hV D id (fun v => hLabelsV v) η)))
    (f : Map U V) (hf : Function.Bijective f) (hΓ : GammaGraphDefinable B (pointMapGraph f))
    (hF : ∀ p, (F.map.map p).val = (f ⟨p.val,p.property⟩).val) (hi : UnaryRelative f 0)
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x)
    (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) x)
    (Q : SelectedLabelFibrePresentation B E.contractedSet (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)) x) :
    let σ := gammaHeadContractedForm T hTargetT A hLabelsU ω
    let τ := gammaHeadContractedForm E hTargetE D hLabelsV η
    Nonempty (GammaFullMeasuredBijection
      (gammaNativeMeasuredLift (gammaUniversalObject P.toGamma) (gammaHeadRawRowForm T hTargetT x P σ))
      (gammaNativeMeasuredLift (gammaUniversalObject Q.toGamma) (gammaHeadRawRowForm E hTargetE x Q τ))) := by
  intro σ τ
  obtain ⟨hfinHT,hTU⟩ := gammaGenericHead_full_measured_fibres (hc := hc) hκ hs h00 hr hv T hU hTargetT hMapT hJacT hfinU A hLabelsU ω
  obtain ⟨hfinHE,hEV⟩ := gammaGenericHead_full_measured_fibres (hc := hc) hκ hs h00 hr hv E hV hTargetE hMapE hJacE hfinV D hLabelsV η
  obtain ⟨gT⟩ := hTU x hx
  obtain ⟨gE⟩ := hEV x hx
  let g := gammaFullMeasuredHeadFibre hU hV hfinU hfinV _ _ F f hf hΓ hF hi x hx
  let pT := gammaHeadRawRowFullMeasuredBridge T hTargetT x P hκ hs hr hv hfinHT σ
  let pE := gammaHeadRawRowFullMeasuredBridge E hTargetE x Q hκ hs hr hv hfinHE τ
  let hrx := small_union_range hκ B.real hr (vfValues x)
  exact ⟨((((pT.comp hκ hs hrx hv (gT.symm hκ hs hrx hv)).comp hκ hs hrx hv g).comp
    hκ hs hrx hv gE).comp hκ hs hrx hv (pE.symm hκ hs hrx hv))⟩

end DiamondIntegral.Section3
