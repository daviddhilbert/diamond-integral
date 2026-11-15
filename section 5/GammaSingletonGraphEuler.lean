import «section 4».GammaFubiniPermutation
import «section 4».GammaGraphIntegration
import «section 4».Section3GammaChartBridge
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The actual Gamma Euler integral of a singleton graph is the integral
of its base, with the output in the last coordinate and no global choice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
open GammaOrderLogic GammaIntegerFamilies GammaIteratedIntegral GammaIndicators GammaWeightedFamilies
open GammaCoordinatePullback GammaFamilyIntegration GammaGraphIntegration
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gamma_singleton_graph_euler
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (I : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (hproj : ∀ η γ, Fin.snoc η γ ∈ K.carrier → η ∈ I.carrier)
    (hrow : ∀ η ∈ I.carrier, ∃! γ, Fin.snoc η γ ∈ K.carrier) :
    integrateAll h00 hκ hs B hr hγ kind (n+1)
      (indicatorFamily B K.carrier (Section3GammaChartBridge.chart K).support_definable) =
    integrateAll h00 hκ hs B hr hγ kind n
      (indicatorFamily B I.carrier (Section3GammaChartBridge.chart I).support_definable) := by
  let hI := (Section3GammaChartBridge.chart I).support_definable
  let hK := (Section3GammaChartBridge.chart K).support_definable
  let f := indicatorFamily B K.carrier hK
  let g := pullback B (finRotate (n+1)) f
  have hfirst : integrateFirst h00 hκ hs B hr hγ kind n g = indicatorFamily B I.carrier hI := by
    apply Subtype.ext
    funext η
    change integralFirst h00 B kind g.val g.property η = (indicatorFamily B I.carrier hI).val η
    have hrot (a : Values.Gamma (M := M)) :
        Fin.cons a η ∘ finRotate (n+1) = Fin.snoc η a := (Fin.snoc_eq_cons_rotate η a).symm
    by_cases hη : η ∈ I.carrier
    · obtain ⟨c, hc, huniq⟩ := hrow η hη
      have he := integralFirst_singleton h00 B kind g.val g.property η c 1 (by
        intro a
        change (if Fin.cons a η ∘ finRotate (n+1) ∈ K.carrier then (1 : ℤ) else 0) = _
        rw [hrot]
        have hmem : Fin.snoc η a ∈ K.carrier ↔ a = c :=
          ⟨fun ha => huniq a ha, fun ha => ha.symm ▸ hc⟩
        rw [hmem]
        by_cases h : a = c <;> simp only [h, ite_true, ite_false])
      simpa only [indicatorFamily, hη, ite_true] using he
    · have he := integralFirst_singleton h00 B kind g.val g.property η 1 0 (by
        intro a
        change (if Fin.cons a η ∘ finRotate (n+1) ∈ K.carrier then (1 : ℤ) else 0) = _
        rw [hrot]
        have hn : Fin.snoc η a ∉ K.carrier := fun ha => hη (hproj η a ha)
        simp only [hn, ite_false, ite_self])
      simpa only [indicatorFamily, hη, ite_false] using he
  have hperm := GammaFubiniPermutation.integrateAll_permutation h00 hκ hs B hr hγ kind
    linear hΓ (n+1) (finRotate (n+1)) f
  calc
    integrateAll h00 hκ hs B hr hγ kind (n+1) f =
        integrateAll h00 hκ hs B hr hγ kind (n+1) g := hperm.symm
    _ = integrateAll h00 hκ hs B hr hγ kind n (indicatorFamily B I.carrier hI) := by
      change integrateAll h00 hκ hs B hr hγ kind n
        (integrateFirst h00 hκ hs B hr hγ kind n g) = _
      rw [hfirst]

end DiamondIntegral.Section5
