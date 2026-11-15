import «section 5».RawRVGammaFamilies
import «section 5».RVGammaFibreEulerValues
import «section 3».GammaGroundRealFibres
import «section 4».GammaIntegralCongruence

/-! Gamma fibre Euler values on raw RV bases, including zeros, are
computed over the exact raw RV parameter base. Nonzero coding preserves
the actual integral by checked base-presentation independence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

theorem rawRVGammaFamily_row_definable
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : Fin p → CanonicalRV.RVSort M) :
    GammaOrderLogic.GammaDefinable ⟨B.real ∪ Set.range (rvValues x),B.gamma⟩ {γ | (x,γ) ∈ T.carrier} := by
  let c : (rawRVSpace (M := M) p).domain := ⟨rvValues x,Set.mem_range_self x⟩
  have h := (T.definable.preimage
    (universalProductSwap ((volumeGammaSpace hc).power (Fin n)) (rawRVSpace p) B.real)).fibreRealPoint c
  have hd : GammaGroundDefinable hc ⟨B.real ∪ Set.range (rvValues x),B.gamma⟩
      ((volumeGammaSpace hc).power (Fin n)) {γ | (x,γ) ∈ T.carrier} := by
    apply h.congr
    intro γ
    have he : (rawRVSpace p).decode c = x := rvValues_injective (rvValues_decode c)
    change ((rawRVSpace p).decode c,γ) ∈ T.carrier ↔ (x,γ) ∈ T.carrier
    rw [he]
  exact (Section3GammaChartBridge.chart ⟨_,hd⟩).support_definable

def rawRVGammaFibreEulerValue
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : Fin p → CanonicalRV.RVSort M) (kind : EulerKind) : ℤ :=
  GammaIteratedIntegral.integrateAll h00 hκ hs ⟨B.real ∪ Set.range (rvValues x),B.gamma⟩
    (small_union_range_carrier hκ B.real hr (rvValues x)) hγ kind n
    (GammaIndicators.indicatorFamily _ {γ | (x,γ) ∈ T.carrier} (rawRVGammaFamily_row_definable T x))

theorem rawRVGammaFibreEulerValue_code
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : rawRVGammaBaseCode X) (kind : EulerKind) :
    rvGammaFibreEulerValue hc h00 hκ hs hr hγ (rawRVGammaFamilyCode h00 X T) x.val kind =
      rawRVGammaFibreEulerValue h00 hκ hs hr hγ T
        (((gammaGroundRVNonzeroTupleCodeBijection h00 X).symm.map x).val) kind := by
  rw [rvGammaFibreEulerValue_integral]
  unfold rawRVGammaFibreEulerValue
  apply GammaIntegralCongruence.integrateAll_congr
  intro γ
  change (if (x.val,γ) ∈ (rawRVGammaFamilyCode h00 X T).carrier then (1 : ℤ) else 0) = _
  rw [rawRVGammaFamilyCode_row]
  rfl

end DiamondIntegral.Section5
