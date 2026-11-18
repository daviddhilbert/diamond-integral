import «section 3».GammaSelectedFinalMeasuredValues
import «section 3».GammaRelativeFirstHeadPropagation

/-! A full relatively unary Gamma-measured bijection has the same
final principal value under the specified aligned head contractions.
The first step is the unary measured comparison; all remaining steps
are the saved positive selected induction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaRelative_ordered_finalValue_eq
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {U V : GammaSelectedRetainedData hc B (n+1) 0}
    (F : GammaFullMeasuredBijection U.zeroSelectedMeasured V.zeroSelectedMeasured)
    (hi : ∀ p, ∀ j, j ≠ 0 → (F.map.map p).val.1 j = p.val.1 j)
    (T : GammaSelectedMeasuredHead U) (E : GammaSelectedMeasuredHead V)
    {A D : GammaSelectedRetainedData hc B 0 (l+1)}
    (tail : GammaSelectedMeasuredOrderedTrace hκ.le hs hr (n := n) (k := 0) (l := l) (T.next hκ.le hs hr) A)
    (etail : GammaSelectedMeasuredOrderedTrace hκ.le hs hr (n := n) (k := 0) (l := l) (E.next hκ.le hs hr) D) :
    A.finalValue hκ.le hs hr hg = D.finalValue hκ.le hs hr hg := by
  exact tail.finalValue_eq hκ.le hs hr hg hκ h00 hv C₀ hBC₀ δ hδ hδ1 etail
    (gammaRelative_first_head_related hκ hs h00 hr hg hv δ hδ hδ1 F hi T E)

end DiamondIntegral.Section3
