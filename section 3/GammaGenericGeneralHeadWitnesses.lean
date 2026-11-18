import «section 3».GammaGenericSelectedHeadWitnesses
import «section 3».GammaFrozenSelectedGenericHeadBridge
import «section 3».GammaGenericUnarySelectedGeometry
import «section 3».GammaMeasuredGeometryFormulaWitnesses
import «section 3».GammaMeasuredNormalizationRows
import Integration7.HeadVolumeParameterContexts

/-! The positive selected head-comparison step follows the RV-density
argument: freeze a generic tail, use the actual unary selected maps and
prepared comparison, then promote the resulting finite geometric proof
back to the complete contracted-family rows over the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a b k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {U : DefSet (M := M) Set.univ (n+1) a} {V : DefSet (M := M) Set.univ (n+1) b}

theorem gammaGeneric_selected_general_head_formula_witness
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (T : HeadPreparation U) (E : HeadPreparation V)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hETarget : GammaSetDefinable B (carrier E.target))
    (hTx : GammaGraphDefinable B (pointMapGraph T.map)) (hEx : GammaGraphDefinable B (pointMapGraph E.map))
    (hJacT : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
      HasMixedVFJacobianAt (Section5.nativeGammaPointBijection (hc := hc) hU
        (gamma_coordinateCanonicalImage T.target hTarget 0)
        (⟨Equiv.ofBijective T.liftMap T.liftMap_bijective,
          gamma_composition_graph T.map (coordinateCanonicalBijection T.target 0) hTx
            (gamma_coordinateCanonical_graph T.target hTarget 0)⟩ : GammaIso B (carrier U) (carrier T.liftSet))).map p 1)
    (hJacE : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
      HasMixedVFJacobianAt (Section5.nativeGammaPointBijection (hc := hc) hV
        (gamma_coordinateCanonicalImage E.target hETarget 0)
        (⟨Equiv.ofBijective E.liftMap E.liftMap_bijective,
          gamma_composition_graph E.map (coordinateCanonicalBijection E.target 0) hEx
            (gamma_coordinateCanonical_graph E.target hETarget 0)⟩ : GammaIso B (carrier V) (carrier E.liftSet))).map p 1)
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b)
    (hfinU : ∀ y t, {r | (y,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinV : ∀ y t, {r | (y,r) ∈ carrier V ∧ r ∘ τ = t}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a)) (R : GammaGroundDefSet hc B (rawRVSpace (M := M) b))
    (hL : ∀ u : U, u.val.2 ∈ Q.carrier) (hK : ∀ v : V, v.val.2 ∈ R.carrier)
    (ω : GammaGroundVolumeForm hc B Q) (η : GammaGroundVolumeForm hc B R) (N L : ℕ)
    (hWitness : ∀ y : Fin (n+1) → VF (M := M), AlgebraicIndependent (vfParameterField B.real) y →
      ∃ H : GammaMeasuredRelationSchema
        (gammaMeasuredBoundedSelectedSchema U hU ρ (gammaPointRetainedForm U hU Q id (fun u => hL u) ω) N).essential
        (gammaMeasuredBoundedSelectedSchema V hV τ (gammaPointRetainedForm V hV R id (fun v => hK v) η) L).essential,
        H.valid (vfValues y))
    (NT NE : ℕ) (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x)
    (hFT : (gammaSelectedHeadSchema T hTarget ρ Q hL ω NT).valid (vfValues x))
    (hFE : (gammaSelectedHeadSchema E hETarget τ R hK η NE).valid (vfValues x)) :
    ∃ H : GammaMeasuredRelationSchema
      (gammaSelectedHeadSchema T hTarget ρ Q hL ω NT).essential
      (gammaSelectedHeadSchema E hETarget τ R hK η NE).essential,
      H.valid (vfValues x) := by
  let Bx : Base (M := M) := ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩
  have hrx : Cardinal.mk Bx.real < κ := small_union_range hκ.le B.real hr (vfValues x)
  let Ux := extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _)
  let Vx := extendBase (coordinateFibre V 0 (headFrozenTuple x)) (Set.subset_univ _)
  let hUx := gammaFrozenHeadPreparation_source hU x
  let hVx := gammaFrozenHeadPreparation_source hV x
  let hfinUx := headFibre_selected_finite U ρ hfinU x
  let hfinVx := headFibre_selected_finite V τ hfinV x
  let Ω := gammaFrozenRetainedForm hU Q hL ω x
  let Ξ := gammaFrozenRetainedForm hV R hK η x
  obtain ⟨NX,hFX⟩ := gammaMeasuredSelectedSchema_uniform_bound hκ.le hs hrx hg Ux hUx ρ Ω hfinUx
  obtain ⟨LX,hGX⟩ := gammaMeasuredSelectedSchema_uniform_bound hκ.le hs hrx hg Vx hVx τ Ξ hfinVx
  have hWX := gammaFrozenSelected_generic_formula_witnesses hU hV ρ τ Q R hL hK ω η N L hWitness x hx NX LX hFX hGX
  have hFinT := head_selected_fibres_finite hκ.le hs hr T hTx hTarget ρ hfinU
  have hFinE := head_selected_fibres_finite hκ.le hs hr E hEx hETarget τ hfinV
  obtain ⟨P⟩ := selectedLabelFibrePresentation_exists T.contractedSet (gamma_headImage T.target hTarget) (headVolumeIndex T ρ) hFinT x
  obtain ⟨S⟩ := selectedLabelFibrePresentation_exists E.contractedSet (gamma_headImage E.target hETarget) (headVolumeIndex E τ) hFinE x
  let P' := gammaFrozenHeadSelectedPresentation T x ρ P
  let S' := gammaFrozenHeadSelectedPresentation E x τ S
  let π := gammaFrozenSelectedHeadForm T hU x ρ P Q hL ω
  let ψ := gammaFrozenSelectedHeadForm E hV x τ S R hK η
  obtain ⟨f,hf⟩ := gammaFrozenSelectedHead_native_measured_bridge_general hκ.le hs hr hv T hU hTarget hTx hJacT ρ hfinU Q hL ω x hx P
  obtain ⟨g,hgTail⟩ := gammaFrozenSelectedHead_native_measured_bridge_general hκ.le hs hr hv E hV hETarget hEx hJacE τ hfinV R hK η x hx S
  let D := headVolumeParameterContext C₀ x
  have hBD : Bx.real ⊆ (D.base : Set M) := head_volume_context_contains_original_base C₀ hBC₀ x
  have hGeo := gammaGeneric_unary_selected_geometry hκ hs h00 hrx hg hv D hBD δ hδ hδ1
    Ux Vx hUx hVx ρ τ hfinUx hfinVx Ω Ξ (gammaUniversalObject P'.toGamma) (gammaUniversalObject S'.toGamma)
    π ψ f g hf hgTail NX LX hFX hGX hWX
  let FT := gammaSelectedHeadSchema T hTarget ρ Q hL ω NT
  let FE := gammaSelectedHeadSchema E hETarget τ R hK η NE
  have rT := gammaMeasured_normalization_row (vfValues x) (gammaUniversalObject P'.toGamma) π FT
    (gammaFrozenSelectedHead_volume T hTarget x ρ P Q hL ω NT)
    (gammaFrozenSelectedHead_density T hU hTarget x ρ P Q hL ω NT)
  have rE := gammaMeasured_normalization_row (vfValues x) (gammaUniversalObject S'.toGamma) ψ FE
    (gammaFrozenSelectedHead_volume E hETarget x τ S R hK η NE)
    (gammaFrozenSelectedHead_density E hV hETarget x τ S R hK η NE)
  exact gammaMeasured_geometry_formula_witness hκ.le hs h00 hr hg (gammaLastMeasuredGeometry_of_native hGeo)
    FT.essential FE.essential (FT.essential_valid _ hFT) (FE.essential_valid _ hFE) rT rE

end DiamondIntegral.Section3
