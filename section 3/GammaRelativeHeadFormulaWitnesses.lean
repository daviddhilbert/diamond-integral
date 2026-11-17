import «section 3».GammaRelativeHeadRowMaps
import «section 3».GammaHeadRawRowSchemaSemantics
import «section 3».GammaUnaryNativeRowWitnesses

/-! A relatively unary measured map supplies uniform bounded head
schemata and finite original-base proof witnesses on every generic VF
tail. All density rows are complete Gamma code classes. -/set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a b : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {U : DefSet (M := M) Set.univ (n+1) a} {V : DefSet (M := M) Set.univ (n+1) b}

theorem gammaRelativeHead_measured_formula_witnesses
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ y z : Section2.VF M, VFValued.predV y z ↔ Valued.v y ≤ Valued.v z)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (T : HeadPreparation U) (E : HeadPreparation V)
    (WT : UniformRelativeTrace Set.univ (n+1) U T.target) (WE : UniformRelativeTrace Set.univ (n+1) V E.target)
    (hWT : GammaUniformTrace (G := B) WT) (hWE : GammaUniformTrace (G := B) WE)
    (hT : ∀ u, WT.toMap u = T.map u) (hE : ∀ u, WE.toMap u = E.map u)
    (hfinU : ∀ x, {r | (x,r) ∈ carrier U}.Finite) (hfinV : ∀ x, {r | (x,r) ∈ carrier V}.Finite)
    (A : GammaGroundDefSet hc B (SpecialTransformations.Section4.rawRVSpace (M := M) a))
    (D : GammaGroundDefSet hc B (SpecialTransformations.Section4.rawRVSpace (M := M) b))
    (hLabelsU : ∀ u : U, u.val.2 ∈ A.carrier) (hLabelsV : ∀ v : V, v.val.2 ∈ D.carrier)
    (ω : GammaGroundVolumeForm hc B A) (η : GammaGroundVolumeForm hc B D)
    (F : GammaFullMeasuredBijection
      (gammaPointMeasuredData U hWT.source hfinU (gammaPointRetainedForm U hWT.source A id (fun u => hLabelsU u) ω))
      (gammaPointMeasuredData V hWE.source hfinV (gammaPointRetainedForm V hWE.source D id (fun v => hLabelsV v) η)))
    (f : Map U V) (hf : Function.Bijective f) (hΓ : GammaGraphDefinable B (pointMapGraph f))
    (hF : ∀ p, (F.map.map p).val = (f ⟨p.val,p.property⟩).val) (hi : UnaryRelative f 0) :
    let hTargetT := (gammaUniformTraceIso WT hWT).target_definable (gammaLogicInput B)
    let hTargetE := (gammaUniformTraceIso WE hWE).target_definable (gammaLogicInput B)
    let σ := gammaHeadContractedForm T hTargetT A hLabelsU ω
    let τ := gammaHeadContractedForm E hTargetE D hLabelsV η
    ∃ NT NE : ℕ,
      let FT := gammaMeasuredBoundedSelectedSchema T.contractedSet (gamma_headImage T.target hTargetT)
        (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) σ NT
      let FE := gammaMeasuredBoundedSelectedSchema E.contractedSet (gamma_headImage E.target hTargetE)
        (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)) τ NE
      (∀ x : Fin n → VF (M := M), FT.valid (vfValues x)) ∧
      (∀ x : Fin n → VF (M := M), FE.valid (vfValues x)) ∧
      ∀ x : Fin n → VF (M := M), AlgebraicIndependent (vfParameterField B.real) x →
        ∃ H : GammaMeasuredRelationSchema FT.essential FE.essential, H.valid (vfValues x) := by
  intro hTargetT hTargetE σ τ
  have hfinU0 (x) (t : Fin 0 → RV (M := M)) :
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ Fin.elim0 = t}.Finite :=
    (hfinU x).subset (fun _ h => h.1)
  have hfinV0 (x) (t : Fin 0 → RV (M := M)) :
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ Fin.elim0 = t}.Finite :=
    (hfinV x).subset (fun _ h => h.1)
  have hFinT := head_selected_fibres_finite hκ.le hs hr T (gammaTracedHead_map_graph T WT hWT hT)
    hTargetT Fin.elim0 hfinU0
  have hFinE := head_selected_fibres_finite hκ.le hs hr E (gammaTracedHead_map_graph E WE hWE hE)
    hTargetE Fin.elim0 hfinV0
  obtain ⟨NT,hNT⟩ := gammaMeasuredSelectedSchema_uniform_bound hκ.le hs hr hg T.contractedSet
    (gamma_headImage T.target hTargetT) (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) σ hFinT
  obtain ⟨NE,hNE⟩ := gammaMeasuredSelectedSchema_uniform_bound hκ.le hs hr hg E.contractedSet
    (gamma_headImage E.target hTargetE) (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)) τ hFinE
  refine ⟨NT,NE,hNT,hNE,?_⟩
  intro x hx
  obtain ⟨P⟩ := selectedLabelFibrePresentation_exists T.contractedSet (gamma_headImage T.target hTargetT)
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) hFinT x
  obtain ⟨Q⟩ := selectedLabelFibrePresentation_exists E.contractedSet (gamma_headImage E.target hTargetE)
    (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)) hFinE x
  obtain ⟨g⟩ := gammaRelativeHead_full_measured_row_map hκ.le hs h00 hr hv T E WT WE hWT hWE hT hE
    hfinU hfinV A D hLabelsU hLabelsV ω η F f hf hΓ hF hi x hx P Q
  exact gammaMeasured_unary_native_lift_row_witness hκ hs h00 hr hg hv δ hδ hδ1 (vfValues x)
    (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma)
    (gammaHeadRawRowForm T hTargetT x P σ) (gammaHeadRawRowForm E hTargetE x Q τ)
    _ _ (hNT x) (hNE x)
    (gammaHeadRawRowSchema_volume T hTargetT x P σ NT) (gammaHeadRawRowSchema_volume E hTargetE x Q τ NE)
    (gammaHeadRawRowSchema_density T hTargetT x P σ NT) (gammaHeadRawRowSchema_density E hTargetE x Q τ NE) g

end DiamondIntegral.Section3
