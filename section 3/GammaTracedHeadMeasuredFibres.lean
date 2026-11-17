import «section 3».GammaTracedHeadMeasuredLifts

/-! The traced head lift restricts to a full unary measured comparison
at every generic frozen VF tail. Its density is the actual contracted
Gamma form, and the frozen tuple is the only added real parameter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {U : DefSet (M := M) Set.univ (n+1) a}

theorem gammaTracedHead_map_graph
    (T : HeadPreparation U) (W : UniformRelativeTrace Set.univ (n+1) U T.target)
    (hWG : GammaUniformTrace (G := B) W) (hW : ∀ u, W.toMap u = T.map u) :
    GammaGraphDefinable B (pointMapGraph T.map) := by
  apply GammaGraphDefinable.congr (GammaUniformTrace.graph W hWG)
  intro x y
  constructor
  · rintro ⟨u,hu,he⟩
    exact ⟨u,hu,(congrArg Subtype.val (hW u)).symm.trans he⟩
  · rintro ⟨u,hu,he⟩
    exact ⟨u,hu,(congrArg Subtype.val (hW u)).trans he⟩

theorem gammaTracedHead_full_measured_fibres
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : HeadPreparation U) (W : UniformRelativeTrace Set.univ (n+1) U T.target)
    (hWG : GammaUniformTrace (G := B) W) (hW : ∀ u, W.toMap u = T.map u)
    (hfin : ∀ x, {r | (x,r) ∈ carrier U}.Finite)
    (Q : GammaGroundDefSet hc B (SpecialTransformations.Section4.rawRVSpace (M := M) a))
    (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    let hTarget := (gammaUniformTraceIso W hWG).target_definable (gammaLogicInput B)
    let Ω := gammaPointRetainedForm U hWG.source Q id (fun u => hLabels u) ω
    let η := gammaHeadLiftForm T hTarget Q hLabels ω
    ∃ hfinH : ∀ x, {r | (x,r) ∈ carrier T.liftSet}.Finite,
      ∀ x : Fin n → VF (M := M), AlgebraicIndependent (vfParameterField B.real) x →
        Nonempty (GammaFullMeasuredBijection
          (gammaHeadMeasuredFibre U hWG.source hfin Ω x)
          (gammaHeadMeasuredFibre T.liftSet (gamma_coordinateCanonicalImage T.target hTarget 0) hfinH η x)) := by
  intro hTarget Ω η
  obtain ⟨hfinH,F,hF⟩ := gammaTracedHead_full_measured_lift (hc := hc) hκ hs h00 hr hv T W hWG hW hfin Q hLabels ω
  have hGraph : GammaGraphDefinable B (pointMapGraph T.liftMap) :=
    gamma_composition_graph T.map (coordinateCanonicalBijection T.target 0)
      (gammaTracedHead_map_graph T W hWG hW) (gamma_coordinateCanonical_graph T.target hTarget 0)
  have hUnary : UnaryRelative T.liftMap 0 := by
    intro u j hj
    exact specialRelative_unaryRelative T.special u j hj
  refine ⟨hfinH,fun x hx => ⟨?_⟩⟩
  exact gammaFullMeasuredHeadFibre hWG.source (gamma_coordinateCanonicalImage T.target hTarget 0)
    hfin hfinH Ω η F T.liftMap T.liftMap_bijective hGraph hF hUnary x hx

end DiamondIntegral.Section3
