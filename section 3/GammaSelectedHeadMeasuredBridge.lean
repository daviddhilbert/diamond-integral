import «section 3».GammaHeadSelectedNativeMeasuredBridge
import «section 3».GammaTracedSelectedHeadMeasuredLifts

/-! A unary head preparation with its actual original-base Jacobian-one
certificate gives the selected full measured native bridge. The source
may have infinite RV fibres before the selected labels are fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {A : DefSet (M := M) Set.univ 1 a}

theorem gammaSelectedHead_native_measured_bridge
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : HeadPreparation A) (hA : GammaSetDefinable B (carrier A))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hJac : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
      HasMixedVFJacobianAt (Section5.nativeGammaPointBijection (hc := hc) hA
        (gamma_coordinateCanonicalImage T.target hTarget 0)
        (⟨Equiv.ofBijective T.liftMap T.liftMap_bijective,
          gamma_composition_graph T.map (coordinateCanonicalBijection T.target 0) hT
            (gamma_coordinateCanonical_graph T.target hTarget 0)⟩ : GammaIso B (carrier A) (carrier T.liftSet))).map p 1)
    (ρ : Fin k → Fin a) (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (P : GammaFiniteGraphPresentation B (1+T.arity) (1+k)
      {r | (Fin.elim0,r) ∈ carrier T.contractedSet}
      (fun r y => (Fin.elim0,r) ∈ carrier T.contractedSet ∧ r ∘ headVolumeIndex T ρ = y))
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hLabels : ∀ u : A, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    ∃ F : GammaFullMeasuredBijection
      (gammaSelectedVFTailMeasuredData A ρ hA hfin (gammaPointRetainedForm A hA Q id (fun u => hLabels u) ω))
      (gammaNativeMeasuredLift (gammaUniversalObject P.toGamma) (gammaHeadSelectedNativeForm T ρ P Q hLabels ω)),
      ∀ p, (F.map.map p).val.1 ∘ Fin.natAdd 1 = p.val.1 ∘ Fin.natAdd 1 := by
  let hH := gamma_coordinateCanonicalImage T.target hTarget 0
  let hΓ := gamma_composition_graph T.map (coordinateCanonicalBijection T.target 0) hT
    (gamma_coordinateCanonical_graph T.target hTarget 0)
  let e : GammaIso B (carrier A) (carrier T.liftSet) := ⟨Equiv.ofBijective T.liftMap T.liftMap_bijective,hΓ⟩
  let Ω := gammaPointRetainedForm A hA Q id (fun u => hLabels u) ω
  let η := gammaHeadLiftForm T hTarget Q hLabels ω
  have hRetained (u : A) : (T.liftMap u).val.2 ∘ headSelectedLabelIndex T ρ = u.val.2 ∘ ρ := by
    have hRV := congrArg Prod.snd (T.lifting_square u)
    have hOld := gammaHeadContractedOldLabels T u
    funext j
    exact (congrFun hRV (headSelectedLabelIndex T ρ j)).trans (congrFun hOld (ρ j))
  have hfinH := finite_selected_rv_fibres_of_gammaIso hκ hs hr e ρ (headSelectedLabelIndex T ρ) hRetained hfin
  let F := gammaSelectedVFTailFullMeasured hκ hs hr hv A T.liftSet ρ (headSelectedLabelIndex T ρ) hA hH
    T.liftMap T.liftMap_bijective hΓ hRetained hfin hfinH Ω η (by
      intro p hp
      refine ⟨1,hJac p hp,?_⟩
      rw [map_one,mul_one]
      let u : A := ⟨p.val,p.property⟩
      have hPoint : (Section5.nativeGammaPointBijection (hc := hc) hA hH e).map p =
          (⟨(T.liftMap u).val,(T.liftMap u).property⟩ : Section5.nativeGammaPointDomain (hc := hc) (carrier T.liftSet) hH) := by
        apply Subtype.ext
        exact Section5.nativeGammaPointBijection_apply (hc := hc) hA hH e p
      rw [hPoint]
      have hForm : Ω p = η ⟨(T.liftMap u).val,(T.liftMap u).property⟩ := by
        apply (gammaHeadLiftForm_apply T hTarget Q hLabels ω u).symm.trans
        congr 1
      exact congrArg (fun v => (cast (gammaCarrier hc) v.val).val) hForm)

  let H := gammaHeadSelectedNativeFullMeasuredBridge T ρ P Q hLabels hκ hs hr hv hTarget hfinH ω
  refine ⟨F.comp hκ hs hr hv (H.symm hκ hs hr hv),?_⟩
  intro p
  have hF := gammaSelectedVFTailBijection_value A ρ hA (headSelectedLabelIndex T ρ) hH
    T.liftMap T.liftMap_bijective hΓ hRetained p
  have hH (q) : (H.map.symm.map q).val = q.val := by
    have he := congrArg Subtype.val (H.map.map.apply_inverse H.map.bijective q)
    exact he
  have hTailF : (F.map.map p).val.1 ∘ Fin.natAdd 1 = p.val.1 ∘ Fin.natAdd 1 := by
    have he := congrArg (fun z : Section2.Mixed M (1+k) (1+T.arity) => z.1 ∘ Fin.natAdd 1) hF
    exact he.trans (funext (Fin.append_right _ _))
  exact (congrArg (fun z : Section2.Mixed M (1+k) (1+T.arity) => z.1 ∘ Fin.natAdd 1)
    (hH (F.map.map p))).trans hTailF

end DiamondIntegral.Section3
