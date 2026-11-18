import «section 3».GammaNativePrefixFullKernel
import «section 3».GammaNativeFullMeasuredPermutations

/-! Full native Gamma-measured bijections changing any one VF coordinate
preserve the original principal class in every positive degree. Actual
coordinate permutations reduce to the checked frozen-prefix comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativeRelativeFullMeasured_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η))
    (i : Fin (n+1)) (hi : ∀ q, ∀ j, j ≠ i → (f.map.map q).val.1 j = q.val.1 j) :
    gammaNativeSpecialClass U ω = gammaNativeSpecialClass V η := by
  let σ : Equiv.Perm (Fin (n+1)) := Equiv.swap i (Fin.last n)
  have hLast : σ (Fin.last n) = i := by simp only [σ,Equiv.swap_apply_right]
  let PU := gammaNativeLiftPermutationFullMeasured hκ.le hs hr hv U σ ω
  let PV := gammaNativeLiftPermutationFullMeasured hκ.le hs hr hv V σ η
  let g := ((PU.symm hκ.le hs hr hv).comp hκ.le hs hr hv f).comp hκ.le hs hr hv PV
  have hFix : ∀ q, (g.map.map q).val.1 ∘ Fin.castAdd 1 = q.val.1 ∘ Fin.castAdd 1 := by
    intro q
    let oldq := (gammaNativeLiftPermutation (hc := hc) U σ).symm.map q
    have hOld : oldq.val.1 = q.val.1 ∘ σ.symm := congrArg Prod.fst (gammaNativeLiftPermutation_inverse_value U σ q)
    change (f.map.map oldq).val.1 ∘ σ ∘ Fin.castAdd 1 = q.val.1 ∘ Fin.castAdd 1
    funext j
    have hne : σ (Fin.castAdd 1 j) ≠ i := by
      intro he
      have hIdx := σ.injective (he.trans hLast.symm)
      have hVal := congrArg Fin.val hIdx
      change j.val = n at hVal
      omega
    exact (hi oldq (σ (Fin.castAdd 1 j)) hne).trans
      ((congrFun hOld (σ (Fin.castAdd 1 j))).trans (congrArg q.val.1 (σ.symm_apply_apply (Fin.castAdd 1 j))))
  have hCompare := gammaNativePrefixFullMeasured_comparison hκ hs h00 hr hg hv C₀ hBC₀ δ hδ hδ1
    (U.reindexVolume σ) (V.reindexVolume σ) (gammaNativePermutedForm U σ ω) (gammaNativePermutedForm V σ η) g hFix
  exact (gammaNativeVolumePermutation_class U σ ω).trans (hCompare.trans (gammaNativeVolumePermutation_class V σ η).symm)

end DiamondIntegral.Section3
