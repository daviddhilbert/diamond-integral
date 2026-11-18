import «section 3».GammaNativePositiveProgramTraces
import «section 3».GammaOrderedSelectedProducts

/-! Heterogeneous endpoint witnesses preserve the literal target and
the complete product, even when the selected-degree expression is
written recursively by the native contraction program. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {W : Type*} [CommMonoid W]

theorem gammaSelectedData_heq_arity {n k l : ℕ}
    {U : GammaSelectedRetainedData hc B n k} {V : GammaSelectedRetainedData hc B n l}
    (hkl : k = l) (h : HEq U V) : U.arity = V.arity := by
  subst l
  cases eq_of_heq h
  rfl

theorem gammaSelectedData_heq_set {n k l : ℕ}
    {U : GammaSelectedRetainedData hc B n k} {V : GammaSelectedRetainedData hc B n l}
    (hkl : k = l) (h : HEq U V) : HEq U.set V.set := by
  subst l
  cases eq_of_heq h
  rfl

theorem gammaSelectedData_heq_select {n k l : ℕ}
    {U : GammaSelectedRetainedData hc B n k} {V : GammaSelectedRetainedData hc B n l}
    (hkl : k = l) (h : HEq U V) : HEq U.select V.select := by
  subst l
  cases eq_of_heq h
  rfl

theorem gammaProduct_heq {a b c : ℕ} {f : Fin a → Fin c} {g : Fin b → Fin c}
    (hab : a = b) (h : HEq f g) (w : Fin c → W) : (∏ i, w (f i)) = ∏ i, w (g i) := by
  subst b
  exact congrArg (fun f => ∏ i, w (f i)) (eq_of_heq h)


theorem gammaSelectedData_heq_form_fibre {k l b : ℕ}
    {U : GammaSelectedRetainedData hc B 0 k} {V : GammaSelectedRetainedData hc B 0 l}
    (hkl : k = l) (h : HEq U V) (r : Point (M := M) 0 b)
    (δ : GammaGroundDefSet.univ hc B (volumeGammaSpace hc))
    (hV : ∀ q : Section5.nativeGammaPointDomain (hc := hc) (carrier V.set) V.gamma,
      HEq q.val r → V.pointForm q = δ)
    (q : Section5.nativeGammaPointDomain (hc := hc) (carrier U.set) U.gamma)
    (hq : HEq q.val r) : U.pointForm q = δ := by
  subst l
  have he := eq_of_heq h
  subst V
  exact hV q hq

end DiamondIntegral.Section3
