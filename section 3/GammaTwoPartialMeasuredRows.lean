import «section 3».GammaFrozenTwoVFMeasuredWitnesses
import «section 3».GammaNativeSelectedTotalRows
import Integration7.TwoPartialVolumeRowComparisons

/-! Two specified partial programs carry generically finite complete
Gamma geometric proofs after freezing the remaining VF coordinates.
The retained density is the same arbitrary original Gamma function. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a l r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaTwo_partial_measured_rows
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {U W : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+2) a}
    {V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n l}
    {Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n r}
    (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ y : Fin (n+2) → VF (M := M), {s | (y,s) ∈ carrier U}.Finite)
    (T : PartialContractionProgram (C.base : Set M) n (n := 2) U V)
    (E : PartialContractionProgram (C.base : Set M) n (n := 2) W Z)
    (hT : GammaPartialProgramDefinable B T) (hE : GammaPartialProgramDefinable B E)
    (τ : Equiv.Perm (Fin 2))
    (hSource : ∀ x : Fin n → VF (M := M), vfPrefixFibre (p := 2) W x =
      vfPermutationImage (vfPrefixFibre (p := 2) U x) τ)
    (hfinV : ∀ x t, {s | (x,s) ∈ carrier V ∧ s ∘ T.volumeIndex = t}.Finite)
    (hfinZ : ∀ x t, {s | (x,s) ∈ carrier Z ∧ s ∘ (E.volumeIndex ∘ τ.symm) = t}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    GammaGenericSelectedRelated
      (gammaNativeSelectedTotalData V (gamma_partial_program_final_set T hT) T.volumeIndex hfinV
        (gammaTotalRVCoordinateForm (suffixIndex T.rvArity_le) ω))
      (gammaNativeSelectedTotalData Z (gamma_partial_program_final_set E hE) (E.volumeIndex ∘ τ.symm) hfinZ
        (gammaTotalRVCoordinateForm (suffixIndex E.rvArity_le) ω)) := by
  let hV := gamma_partial_program_final_set T hT
  let hZ := gamma_partial_program_final_set E hE
  let Ω := gammaTotalRVCoordinateForm (suffixIndex T.rvArity_le) ω
  let Ξ := gammaTotalRVCoordinateForm (suffixIndex E.rvArity_le) ω
  let D := gammaNativeSelectedTotalData V hV T.volumeIndex hfinV Ω
  let K := gammaNativeSelectedTotalData Z hZ (E.volumeIndex ∘ τ.symm) hfinZ Ξ
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  obtain ⟨N,hN⟩ := D.uniform_bound C.uncountable.le C.saturated hr hg
  obtain ⟨L,hL⟩ := K.uniform_bound C.uncountable.le C.saturated hr hg
  refine ⟨N,L,hN,hL,?_⟩
  intro x hx
  let A := vfPrefixFibre (p := 2) U x
  have hA := gamma_vfPrefixFibre (p := 2) U hU x
  let R := standardFromProgram A (Equiv.refl _) (restrictPartialToPrefix T x) (vfPermutationImage_id_eq A).symm
  let S := standardFromProgram A τ (restrictPartialToPrefix E x) (hSource x)
  have hR := gamma_standardFromProgram A (Equiv.refl _) (restrictPartialToPrefix T x)
    (vfPermutationImage_id_eq A).symm (gamma_restrictPartialToPrefix T hT x)
  have hS := gamma_standardFromProgram A τ (restrictPartialToPrefix E x) (hSource x)
    (gamma_restrictPartialToPrefix E hE x)
  have hfinA : ∀ y : Fin 2 → VF (M := M), {s | (y,s) ∈ carrier A}.Finite :=
    fun y => hfinU (vfPrefixTuple x y)
  have hRV : R.volumeIndex = T.volumeIndex := by
    funext i
    exact (standard_from_program_volume_index (Equiv.refl _) _ _ i).trans
      (congrFun (restrict_partial_prefix_volume_index T x) i)
  have hSV : S.volumeIndex = E.volumeIndex ∘ τ.symm := by
    funext i
    exact (standard_from_program_volume_index τ _ _ i).trans
      (congrFun (restrict_partial_prefix_volume_index E x) (τ.symm i))
  have hMemR (s : Fin l → RV (M := M)) :
      (Fin.elim0,s) ∈ carrier R.target ↔ (x,s) ∈ carrier V := by
    change (vfPrefixTuple x Fin.elim0,s) ∈ carrier V ↔ _
    rw [vfPrefixTuple_zero]
  have hMemS (s : Fin r → RV (M := M)) :
      (Fin.elim0,s) ∈ carrier S.target ↔ (x,s) ∈ carrier Z := by
    change (vfPrefixTuple x Fin.elim0,s) ∈ carrier Z ↔ _
    rw [vfPrefixTuple_zero]
  let ωx : GammaGroundVolumeForm hc ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩
      (GammaGroundDefSet.univ hc ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (rawRVSpace (M := M) a)) :=
    ω.monoReal Set.subset_union_left
  apply gammaFrozen_two_VF_measured_witness C hBC hv hg hNames hGenerated δ hδ hδ1 x A hA hfinA
    ωx R S hR hS (D.schema N) (K.schema L) (hN x) (hL x)
  · intro s y
    have h := gammaNativeSelectedTotal_volume V hV T.volumeIndex hfinV Ω N x s y
    exact h.trans (and_congr (hMemR s).symm (Iff.of_eq (congrArg (fun ρ => s ∘ ρ = y) hRV.symm)))
  · intro s y
    have h := gammaNativeSelectedTotal_volume Z hZ (E.volumeIndex ∘ τ.symm) hfinZ Ξ L x s y
    exact h.trans (and_congr (hMemS s).symm (Iff.of_eq (congrArg (fun ρ => s ∘ ρ = y) hSV.symm)))
  · intro s c
    have h := gammaNativeSelectedTotal_density V hV T.volumeIndex hfinV Ω N x s c
    exact h.trans (and_congr (hMemR s).symm Iff.rfl)
  · intro s c
    have h := gammaNativeSelectedTotal_density Z hZ (E.volumeIndex ∘ τ.symm) hfinZ Ξ L x s c
    exact h.trans (and_congr (hMemS s).symm Iff.rfl)

end DiamondIntegral.Section3
