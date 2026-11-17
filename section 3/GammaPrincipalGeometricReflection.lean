import «section 3».GammaPointConeProductGeometry
import «section 3».GammaMeasuredIndexedGeometry
import «section 3».PrincipalAdditiveContextDescent
import «section 3».GammaGroundMeasuredRVGradingConsequences

/-! The actual principal congruence has finite geometric witnesses in
each homogeneous positive degree. The checked direct-sum grading extracts
that degree; native point/cone product charts handle every coefficient.
The argument stays in semirings throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {W : Type*} [AddCommMonoid W]

theorem gammaMeasuredGeometric_preserves_additive
    {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}
    {h00 : M ⊨ Axioms.ACVF00} {hr : Cardinal.mk B.real < κ}
    (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    {U V : GammaGroundMeasuredRVObject hc B (n+1)}
    (h : GammaMeasuredGeometricRelation hκ hs h00 hr U V) :
    χ (gammaGroundMeasuredRVClass U) = χ (gammaGroundMeasuredRVClass V) := by
  induction h with
  | iso e => obtain ⟨e⟩ := e; exact congrArg χ (gammaGroundMeasuredRVClass_iso e)
  | elementary A ω i hAd => exact hχ A ω i hAd
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | coprod h k ih ik =>
    rw [gammaGroundMeasuredRVClass_coprod,gammaGroundMeasuredRVClass_coprod,χ.map_add,χ.map_add,ih,ik]

def gammaMeasuredDegreeCoefficient (d : ℕ) :
    GammaGroundMeasuredRVPositiveSemiring hc B →+ GammaGroundMeasuredRVKPlus hc B d where
  toFun a := (gammaGroundMeasuredRVPresentationToDirectSum a) d
  map_zero' := by
    change (gammaGroundMeasuredRVPresentationToDirectSum (0 : GammaGroundMeasuredRVPositiveSemiring hc B)) d = 0
    exact congrArg (fun s : GammaGroundMeasuredRVDirectSum hc B => s d)
      (gammaGroundMeasuredRVPresentationToDirectSum (M := M) (hc := hc) (ground := B)).map_zero
  map_add' a b := by
    change (gammaGroundMeasuredRVPresentationToDirectSum (a+b)) d =
      (gammaGroundMeasuredRVPresentationToDirectSum a) d + (gammaGroundMeasuredRVPresentationToDirectSum b) d
    exact congrArg (fun s : GammaGroundMeasuredRVDirectSum hc B => s d)
      ((gammaGroundMeasuredRVPresentationToDirectSum (M := M) (hc := hc) (ground := B)).map_add a b)

theorem gammaMeasuredDegreeCoefficient_class (d : ℕ) (U : GammaGroundMeasuredRVObject hc B d) :
    gammaMeasuredDegreeCoefficient d (gammaGroundMeasuredRVSemiringClass U) = gammaGroundMeasuredRVClass U := by
  change (gammaGroundMeasuredRVPresentationToDirectSum (gammaGroundMeasuredRVSemiringClass U)) d = _
  rw [gammaGroundMeasuredRVPresentationToDirectSum_class]
  exact DirectSum.of_eq_same d _

theorem gammaMeasuredDegreeCoefficient_other {d k : ℕ} (hdk : d ≠ k)
    (U : GammaGroundMeasuredRVObject hc B k) :
    gammaMeasuredDegreeCoefficient d (gammaGroundMeasuredRVSemiringClass U) = 0 := by
  change (gammaGroundMeasuredRVPresentationToDirectSum (gammaGroundMeasuredRVSemiringClass U)) d = _
  rw [gammaGroundMeasuredRVPresentationToDirectSum_class]
  exact DirectSum.of_eq_of_ne k d _ hdk

theorem gammaMeasuredDegree_additive_principal_context
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (a : GammaGroundMeasuredRVPositiveSemiring hc B) :
    (χ.comp (gammaMeasuredDegreeCoefficient (n+1)))
        (a * gammaGroundMeasuredRVSemiringClass (gammaGroundMeasuredRVOne hc B)) =
      (χ.comp (gammaMeasuredDegreeCoefficient (n+1)))
        (a * gammaGroundMeasuredRVSemiringClass (gammaGroundMeasuredRVPositive hc B)) := by
  let F := gammaGroundMeasuredRVPresentationToDirectSum (M := M) (hc := hc) (ground := B)
  let back := gammaGroundMeasuredRVDirectSumToPresentation (M := M) (hc := hc) (ground := B)
  let φ := χ.comp (gammaMeasuredDegreeCoefficient (n+1))
  have hBF : back.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (gammaGroundMeasuredRVSemiringPresentation hc B)
    rintro ⟨k,U⟩
    change back (F (gammaGroundMeasuredRVSemiringClass U)) = gammaGroundMeasuredRVSemiringClass U
    rw [gammaGroundMeasuredRVPresentationToDirectSum_class,gammaGroundMeasuredRVDirectSumToPresentation_class]
  have ha : back (F a) = a := RingHom.congr_fun hBF a
  rw [← ha]
  generalize F a = b
  change φ (back b * _) = φ (back b * _)
  induction b using DirectSum.induction_on with
  | zero => rw [back.map_zero,zero_mul,zero_mul]
  | of k b =>
    obtain ⟨U,rfl⟩ := gammaGroundMeasuredRVClass_surjective b
    change φ (back (gammaGroundMeasuredRVDirectSumClass U) * _) =
      φ (back (gammaGroundMeasuredRVDirectSumClass U) * _)
    rw [gammaGroundMeasuredRVDirectSumToPresentation_class,
      ← gammaGroundMeasuredRVSemiringClass_product,← gammaGroundMeasuredRVSemiringClass_product]
    change χ (gammaMeasuredDegreeCoefficient (n+1) (gammaGroundMeasuredRVSemiringClass (U.product (gammaGroundMeasuredRVOne hc B)))) =
      χ (gammaMeasuredDegreeCoefficient (n+1) (gammaGroundMeasuredRVSemiringClass (U.product (gammaGroundMeasuredRVPositive hc B))))
    by_cases hk : k = n
    · subst k
      rw [gammaMeasuredDegreeCoefficient_class,gammaMeasuredDegreeCoefficient_class]
      exact gammaMeasuredGeometric_preserves_additive χ hχ (gammaPoint_cone_product_geometric hκ hs h00 hr U)
    · have hne : n+1 ≠ k+1 := fun h => hk (Nat.succ.inj h.symm)
      rw [gammaMeasuredDegreeCoefficient_other hne,gammaMeasuredDegreeCoefficient_other hne]
  | add b c ih ik =>
    rw [back.map_add,add_mul,add_mul,φ.map_add,φ.map_add,ih,ik]

theorem gammaPrincipal_preserves_fixed_degree_additive
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    {U V : GammaGroundMeasuredRVObject hc B (n+1)}
    (h : gammaMeasuredPrincipalValue U = gammaMeasuredPrincipalValue V) :
    χ (gammaGroundMeasuredRVClass U) = χ (gammaGroundMeasuredRVClass V) := by
  have H := principal_additive_descent (χ.comp (gammaMeasuredDegreeCoefficient (n+1)))
    (gammaGroundMeasuredRVSemiringClass (gammaGroundMeasuredRVOne hc B))
    (gammaGroundMeasuredRVSemiringClass (gammaGroundMeasuredRVPositive hc B))
    (gammaMeasuredDegree_additive_principal_context hκ hs h00 hr χ hχ)
    ((gammaGroundMeasuredRVSpecialCongruence hc B).eq.mp h)
  change χ (gammaMeasuredDegreeCoefficient (n+1) (gammaGroundMeasuredRVSemiringClass U)) =
    χ (gammaMeasuredDegreeCoefficient (n+1) (gammaGroundMeasuredRVSemiringClass V)) at H
  simpa only [gammaMeasuredDegreeCoefficient_class] using H

theorem gammaPrincipal_geometric_reflection
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    {U V : GammaGroundMeasuredRVObject hc B (n+1)}
    (h : gammaMeasuredPrincipalValue U = gammaMeasuredPrincipalValue V) :
    GammaMeasuredGeometricRelation hκ hs h00 hr U V := by
  let q : GammaGroundMeasuredRVKPlus hc B (n+1) →+
      (gammaNativeGeometricCongruence (hc := hc) (B := B) (n := n) hκ hs h00 hr).Quotient :=
    (gammaNativeGeometricCongruence (hc := hc) (B := B) (n := n) hκ hs h00 hr).mk'
  have hq := gammaPrincipal_preserves_fixed_degree_additive
    (W := (gammaNativeGeometricCongruence (hc := hc) (B := B) (n := n) hκ hs h00 hr).Quotient)
    (hc := hc) (B := B) (n := n) hκ hs h00 hr q
    (gammaNativeGeometricQuotient_elementary (hc := hc) (B := B) (n := n) hκ hs h00 hr) h
  exact gammaMeasuredGeometricRelation_of_additive_derivation
    ((gammaNativeGeometricCongruence hκ hs h00 hr).eq.mp hq) U V rfl rfl

end DiamondIntegral.Section3
