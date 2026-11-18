import «section 3».GammaArbitraryMeasuredContractionOrders

/-! With no initially selected RV coordinates, the selected comparison
is exactly arbitrary-order comparison of the full raw measured standard
contractions. The proof retains complete Gamma densities and zero rows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}

theorem gammaRaw_empty_selected_measured_value
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (hfin0 : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ (Fin.elim0 : Fin 0 → Fin a) = t}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    gammaMeasuredPrincipalValue (gammaNativeRawSelectedMeasuredContraction C hBC hA Fin.elim0 hfin0 T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) := by
  let U := gammaNativeRawSelectedAt C hBC hA Fin.elim0 hfin0 T hT
  let V := gammaNativeFiniteAt (gammaRawFiniteContraction C.uncountable.le C.saturated
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hBC hA hfin T hT)
  have hDom : (Section5.nativeRVGroundDomain (hc := hc) U).carrier =
      (Section5.nativeRVGroundDomain (hc := hc) V).carrier := by
    ext r
    rw [gammaNativeRawSelected_mem,gammaNative_raw_contraction_mem]
  let f := GammaGroundBijection.ofCarrierEq hDom
  apply gammaNative_heterogeneous_measured_value (Nat.zero_add n) U V
    (gammaNativeTotalRVForm U (suffixIndex T.program.rvArity_le) ω)
    (gammaNativeTotalRVForm V (suffixIndex T.program.rvArity_le) ω) f
  · intro u
    rw [gammaNativeRawSelected_volume,gammaNativeRVGroundVolume_value]
    change (∏ i, Values.vrv (u.val (selectedStandardVolumeIndex T Fin.elim0 i))) =
      ∏ i, Values.vrv (u.val (T.volumeIndex i))
    have hReindex := Equiv.prod_comp (finCongr (Nat.add_comm 0 (n+1)))
      (fun j => Values.vrv (u.val (Fin.append T.volumeIndex
        (suffixIndex T.program.rvArity_le ∘ (Fin.elim0 : Fin 0 → Fin a)) j)))
    apply hReindex.trans
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left,Fin.prod_univ_zero,mul_one]
  · intro u
    rfl

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaFull_raw_all_order_measured_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    {σ τ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (E : StandardContraction A τ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin E hE ω) := by
  let hfin0 := fun x t => (hfin x).subset
    (fun r (hr : (x,r) ∈ carrier A ∧ r ∘ (Fin.elim0 : Fin 0 → Fin a) = t) => hr.1)
  have hMiddle := gammaSelected_all_order_measured_values C hBC hv hg hNames hGenerated δ hδ hδ1 n
    A hA Fin.elim0 hfin0 ω σ τ T E hT hE
  have hLeft := gammaRaw_empty_selected_measured_value C hBC hA hfin hfin0 T hT ω
  have hRight := gammaRaw_empty_selected_measured_value C hBC hA hfin hfin0 E hE ω
  exact hLeft.symm.trans (hMiddle.trans hRight)

end DiamondIntegral.Section3
