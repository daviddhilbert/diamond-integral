import «section 3».GammaGenericRawFamilyComparison
import «section 3».GammaNativePreparedSliceComparison
import «section 3».GammaUnaryLiftRowComparisons

/-! Generic actual comparisons of unary volume-slice lifts imply equality
of the original higher-degree principal classes. The indexed-family bridge
and every density graph remain over the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNative_unary_slice_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U V : GammaObjectAt B Set.univ (p+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V)) (N L : ℕ)
    (hFV : ∀ x : Fin p → VF (M := M), (gammaNativeMeasuredVFSliceSchema U ω N).valid (vfValues x))
    (hGV : ∀ x : Fin p → VF (M := M), (gammaNativeMeasuredVFSliceSchema V η L).valid (vfValues x))
    (hFibres : ∀ x : Fin p → VF (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      gammaUnaryMeasuredRowLiftComparison (gammaNativeMeasuredVFSliceSchema U ω N)
        (gammaNativeMeasuredVFSliceSchema V η L) (vfValues x)) :
    gammaNativeSpecialClass U ω = gammaNativeSpecialClass V η := by
  let F := gammaNativeMeasuredVFSliceSchema U ω N
  let G := gammaNativeMeasuredVFSliceSchema V η L
  have hWitness : ∀ x : Fin p → VF (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaMeasuredRelationSchema F.essential G.essential, H.valid (vfValues x) := by
    intro x hx
    exact gammaMeasured_unary_raw_row_witness hκ hs h00 hr hg hv δ hδ hδ1 F G (vfValues x) (hFibres x hx)
  let A : DefSet (M := M) (C₀.base : Set M) p 0 := PresentedSet.univ (pointSpace p 0) (C₀.base : Set M)
  have hA : GammaSetDefinable B (carrier A) :=
    (gammaLogicInput B).real_set _ (setDefinable (PresentedSet.univ (pointSpace p 0) B.real))
  obtain ⟨D,hCD,l,Z,T,hT,hZ,BP,hFA,hGA,hF,hG,hEq⟩ :=
    gammaGeneric_raw_prepared_family_comparison hκ.le hs h00 hr hg C₀ hBC₀ A hA F G hFV hGV hWitness
  let P := (F.recode (GammaParameterRecode.prepared T hT)).object.indexedPresentation_finiteRows BP
    (fun t ht => (F.recode (GammaParameterRecode.prepared T hT)).object.finiteRow_of_valid _ (hF t ht).1)
  let Q := (G.recode (GammaParameterRecode.prepared T hT)).object.indexedPresentation_finiteRows BP
    (fun t ht => (G.recode (GammaParameterRecode.prepared T hT)).object.finiteRow_of_valid _ (hG t ht).1)
  have hU := gammaNativePreparedSlice_comparison hκ.le hs h00 hr hg hv C₀ hBC₀ U ω N hFV T hT hZ
    (fun _ => Set.mem_univ _) hFA BP P
  have hV := gammaNativePreparedSlice_comparison hκ.le hs h00 hr hg hv C₀ hBC₀ V η L hGV T hT hZ
    (fun _ => Set.mem_univ _) hGA BP Q
  exact hU.trans ((hEq P Q).trans hV.symm)

end DiamondIntegral.Section3
