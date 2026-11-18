import «section 3».GammaStandardRawLabelCutComparisons
import «section 3».GammaMeasuredLiteralNormalizationRows

/-! Raw contraction rows expose their actual target, all structural
volume coordinates and complete retained Gamma form independently of
the formula's parameter presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B D : Base (M := M)}
variable {n a p : ℕ} {sp : Fin p → SortTag}

theorem gammaRaw_contraction_literal_row
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ)
    (hT : GammaProgramDefinable B T.program)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    (F : GammaMeasuredRVSchema hc D p T.arity (n+1) sp) (z : Fin p → M)
    (hVol : ∀ r y, F.object.rowVolume z r y ↔ (Fin.elim0,r) ∈ carrier T.target ∧ r ∘ T.volumeIndex = y)
    (hDensity : ∀ r c, F.rowDensity z r c ↔ (Fin.elim0,r) ∈ carrier T.target ∧
      (ω ⟨r ∘ suffixIndex T.program.rvArity_le,Set.mem_univ _⟩).val = (volumeGammaSpace hc).decode c) :
    GammaMeasuredLiteralObjectRow z (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) F.essential := by
  let U := gammaNativeFiniteAt (gammaRawFiniteContraction C.uncountable.le C.saturated
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hBC hA hfin T hT)
  let η := gammaNativeTotalRVForm U (suffixIndex T.program.rvArity_le) ω
  apply gammaMeasured_normalization_literal_row z U η F
  · intro r y
    rw [hVol]
    constructor
    · rintro ⟨hr,hy⟩
      let u : Section5.nativeRVGroundDomain (hc := hc) U :=
        ⟨r,(gammaNative_raw_contraction_mem (hc := hc) C hBC hA hfin T hT r).mpr hr⟩
      refine ⟨u,rfl,?_⟩
      rw [gammaNativeRVGroundVolume_value]
      exact hy
    · rintro ⟨u,hu,hy⟩
      refine ⟨hu ▸ (gammaNative_raw_contraction_mem (hc := hc) C hBC hA hfin T hT u.val).mp u.property,?_⟩
      rw [gammaNativeRVGroundVolume_value] at hy
      exact hu ▸ hy
  · intro r c
    rw [hDensity]
    constructor
    · rintro ⟨hr,hω⟩
      exact ⟨⟨r,(gammaNative_raw_contraction_mem (hc := hc) C hBC hA hfin T hT r).mpr hr⟩,rfl,hω⟩
    · rintro ⟨u,hu,hω⟩
      exact ⟨hu ▸ (gammaNative_raw_contraction_mem (hc := hc) C hBC hA hfin T hT u.val).mp u.property,hu ▸ hω⟩

end DiamondIntegral.Section3
