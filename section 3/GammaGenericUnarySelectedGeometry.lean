import «section 3».GammaSelectedUnaryPreparedGeometry
import «section 3».GammaGenericRawFamilyAdditive

/-! The unary positive selected-family step of the RV-density induction
holds for complete Gamma density graphs and finite geometric witnesses
at generic parameters. Both endpoints are the specified actual lifts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a b k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaGeneric_unary_selected_geometry
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U : DefSet (M := M) Set.univ 1 a) (V : DefSet (M := M) Set.univ 1 b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b)
    (hfinU : ∀ x t, {r | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinV : ∀ x t, {r | (x,r) ∈ carrier V ∧ r ∘ τ = t}.Finite)
    (Ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier U) hU))
    (Ξ : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier V) hV))
    (P Q : GammaObjectAt B Set.univ (1+(k+1)))
    (π : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain P))
    (ψ : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain Q))
    (f : GammaFullMeasuredBijection (gammaSelectedVFTailMeasuredData U ρ hU hfinU Ω) (gammaNativeMeasuredLift P π))
    (g : GammaFullMeasuredBijection (gammaSelectedVFTailMeasuredData V τ hV hfinV Ξ) (gammaNativeMeasuredLift Q ψ))
    (hf : ∀ p, (f.map.map p).val.1 ∘ Fin.natAdd 1 = p.val.1 ∘ Fin.natAdd 1)
    (hgTail : ∀ p, (g.map.map p).val.1 ∘ Fin.natAdd 1 = p.val.1 ∘ Fin.natAdd 1)
    (N L : ℕ)
    (hF : ∀ x : Fin 1 → VF (M := M), (gammaMeasuredBoundedSelectedSchema U hU ρ Ω N).valid (vfValues x))
    (hE : ∀ x : Fin 1 → VF (M := M), (gammaMeasuredBoundedSelectedSchema V hV τ Ξ L).valid (vfValues x))
    (hWitness : ∀ x : Fin 1 → VF (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaMeasuredRelationSchema (gammaMeasuredBoundedSelectedSchema U hU ρ Ω N).essential
        (gammaMeasuredBoundedSelectedSchema V hV τ Ξ L).essential, H.valid (vfValues x)) :
    GammaMeasuredGeometricRelation hκ.le hs h00 hr (gammaNativeMeasuredNormalization P π) (gammaNativeMeasuredNormalization Q ψ) := by
  let F := gammaMeasuredBoundedSelectedSchema U hU ρ Ω N
  let E := gammaMeasuredBoundedSelectedSchema V hV τ Ξ L
  let A : DefSet (M := M) (C₀.base : Set M) 1 0 := PresentedSet.univ (pointSpace 1 0) (C₀.base : Set M)
  have hA : GammaSetDefinable B (carrier A) :=
    (gammaLogicInput B).real_set _ (setDefinable (PresentedSet.univ (pointSpace 1 0) B.real))
  let χ : GammaGroundMeasuredRVKPlus hc B (1+(k+1)) →+
      (gammaNativeGeometricCongruence (hc := hc) (B := B) (n := 1+k) hκ.le hs h00 hr).Quotient :=
    (gammaNativeGeometricCongruence (hc := hc) (B := B) (n := 1+k) hκ.le hs h00 hr).mk'
  have hχ : GammaNativeElementaryInvariant (hc := hc) (B := B) (n := 1+k)
      (W := (gammaNativeGeometricCongruence (hc := hc) (B := B) (n := 1+k) hκ.le hs h00 hr).Quotient)
      hκ.le hs h00 hr χ :=
    gammaNativeGeometricQuotient_elementary (hc := hc) (B := B) (n := 1+k) hκ.le hs h00 hr
  obtain ⟨D,hCD,l,Z,T,hT,hZ,BP,hFA,hEA,hFR,hER,hEq⟩ :=
    gammaGeneric_raw_prepared_family_additive_comparison (hc := hc) (B := B) (p := 1) (k := k)
      (W := (gammaNativeGeometricCongruence (hc := hc) (B := B) (n := 1+k) hκ.le hs h00 hr).Quotient) hκ.le hs h00 hr hg χ hχ
      C₀ hBC₀ A hA F E hF hE hWitness
  let R := (F.recode (GammaParameterRecode.prepared T hT)).object.indexedPresentation_finiteRows BP
    (fun t ht => (F.recode (GammaParameterRecode.prepared T hT)).object.finiteRow_of_valid _ (hFR t ht).1)
  let S := (E.recode (GammaParameterRecode.prepared T hT)).object.indexedPresentation_finiteRows BP
    (fun t ht => (E.recode (GammaParameterRecode.prepared T hT)).object.finiteRow_of_valid _ (hER t ht).1)
  have hLeft := gammaSelectedUnary_prepared_geometric_relation hκ hs h00 hr hg hv C₀ hBC₀ δ hδ hδ1
    U hU ρ hfinU Ω P π f hf N hF T hT hZ hFA (fun _ => Set.mem_univ _) BP R
  have hRight := gammaSelectedUnary_prepared_geometric_relation hκ hs h00 hr hg hv C₀ hBC₀ δ hδ hδ1
    V hV τ hfinV Ξ Q ψ g hgTail L hE T hT hZ hEA (fun _ => Set.mem_univ _) BP S
  have hMain := gammaMeasuredGeometricRelation_of_additive_derivation
    ((gammaNativeGeometricCongruence (hc := hc) (B := B) (n := 1+k) hκ.le hs h00 hr).eq.mp (hEq R S)) _ _ rfl rfl
  exact hLeft.trans (hMain.trans hRight.symm)

end DiamondIntegral.Section3
