import «section 3».GammaRelativeHeadFormulaWitnesses
import «section 3».GammaPreparedFamilyComparisons

/-! Relatively unary full measured maps give prepared principal
comparisons of the actual retained Gamma head families. The conclusion
uses total degree n+1 and stays over the original base. -/
set_option autoImplicit false
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

theorem gammaRelativeHead_prepared_family_comparison
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
    (hF : ∀ p, (F.map.map p).val = (f ⟨p.val,p.property⟩).val) (hi : UnaryRelative f 0)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (X₀ : DefSet (M := M) (C₀.base : Set M) n 0) (hX₀ : GammaSetDefinable B (carrier X₀)) :
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
      GammaPreparedMeasuredFamilyComparison C₀ X₀ FT.essential FE.essential := by
  intro hTargetT hTargetE σ τ
  obtain ⟨NT,NE,hNT,hNE,hWitness⟩ := gammaRelativeHead_measured_formula_witnesses hκ hs h00 hr hg hv δ hδ hδ1
    T E WT WE hWT hWE hT hE hfinU hfinV A D hLabelsU hLabelsV ω η F f hf hΓ hF hi
  refine ⟨NT,NE,hNT,hNE,?_⟩
  exact gammaPreparedMeasuredFamilyComparison_of_generic hκ.le hs h00 hr hg C₀ hBC₀ X₀ hX₀ _ _ hWitness

end DiamondIntegral.Section3
