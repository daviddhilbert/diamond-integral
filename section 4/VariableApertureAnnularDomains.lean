import «section 4».VariableApertureRayCancellation
import «section 4».RVBoundedCharts

/-! Exact variable annulus membership and its actual RV-domain bounds.
The retained aperture coordinate may have infinite image. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4

namespace DiamondIntegral.Section4.VariableApertureRayCancellation
open RVMeasuredCharts RVMeasuredProduct RVRealProducts FiniteTupleBlocks
open RVCoefficientShearGraphs RVNamedMultiplication RVScaledRays GammaGroupNames

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

theorem deepDomain_join_iff (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j))
    (x : Fin r.arity → M) (hx : x ∈ r.domain)
    (z : Fin 1 → M) (hz : Proper z) :
    join 1 r.arity x z ∈ deepDomain r j ↔ codeValue (x j) < codeValue (z 0) := by
  constructor
  · rintro ⟨u,hu,he⟩
    obtain ⟨y,hy,w,hw,rfl⟩ := (productSet_exists r.domain _ u).mp hu
    change Proper w ∧ 1 < codeValue (w 0) at hw
    rw [shear_join] at he
    have hyx : y=x := by
      funext i
      have h := congrFun he (headIndex 1 r.arity i)
      simpa only [join_head] using h
    subst y
    have hez : scale (x j) w=z := by
      funext i
      have h := congrFun he (tailIndex 1 r.arity i)
      simpa only [join_tail] using h
    rw [← hez]
    change codeValue (x j) < codeValue (iRVMul (x j) (w 0))
    rw [codeValue_mul _ _ (hp x hx) (hw.1 0)]
    simpa only [mul_one] using mul_lt_mul_right hw.2 (codeValue (x j))
  · intro hlt
    let t := RVCoefficientTranslation.coefficientCode j x (hp x hx)
    let w := scale (raw (inverseCode t)) z
    have hw0 : NonzeroRV (w 0) := scale_nonzero (inverseCode t) (hz 0)
    have hw : w ∈ (RVSharpCharts.sharpChart (RVMeasuredSpecialClasses.rayChart B)).domain := by
      refine ⟨(by intro i; fin_cases i; exact hw0),?_⟩
      change 1 < codeValue (iRVMul (raw (inverseCode t)) (z 0))
      rw [codeValue_mul _ _ ⟨raw_rv _,raw_ne_zero _⟩ (hz 0),inverseCode_value]
      have ht : value t=codeValue (x j) := RVCoefficientTranslation.coefficientCode_value j x (hp x hx)
      rw [ht]
      have h := mul_lt_mul_right hlt (codeValue (x j))⁻¹
      simpa only [inv_mul_cancel] using h
    refine ⟨join 1 r.arity x w,(productSet_join _ _ _ _).mpr ⟨hx,hw⟩,?_⟩
    rw [shear_join]
    exact congrArg (join 1 r.arity x) (scale_inverse t z (hz 0).1)

theorem annularChart_join_iff (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j))
    (x : Fin r.arity → M) (z : Fin 1 → M) :
    join 1 r.arity x z ∈ (annularChart r j).domain ↔
      x ∈ r.domain ∧ Proper z ∧ 1 < codeValue (z 0) ∧ codeValue (z 0) ≤ codeValue (x j) := by
  constructor
  · intro h
    have hP := (productSet_join r.domain _ x z).mp h.1
    change x ∈ r.domain ∧ Proper z ∧ 1 < codeValue (z 0) at hP
    refine ⟨hP.1,hP.2.1,hP.2.2,?_⟩
    exact le_of_not_gt (fun he => h.2 ((deepDomain_join_iff r j hp x hP.1 z hP.2.1).mpr he))
  · rintro ⟨hx,hz,hpos,hle⟩
    refine ⟨(productSet_join _ _ _ _).mpr ⟨hx,hz,hpos⟩,?_⟩
    exact fun h => not_lt_of_ge hle ((deepDomain_join_iff r j hp x hx z hz).mp h)

theorem annularChart_domain_bounded (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j))
    (hr : RVMeasuredBounds.DomainBounded r) (Δ : Values.Gamma (M := M))
    (hΔ : ∀ x ∈ r.domain, codeValue (x j) ≤ Δ) :
    RVMeasuredBounds.DomainBounded (annularChart r j) := by
  obtain ⟨β,hβ⟩ := hr
  let η := max β (max Δ 1)
  have hβη : β ≤ η := le_max_left _ _
  have hΔη : Δ ≤ η := (le_max_left _ _).trans (le_max_right _ _)
  have h1η : (1 : Values.Gamma (M := M)) ≤ η :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨η,?_⟩
  intro u hu i hi
  let x := u ∘ headIndex 1 r.arity
  let z := u ∘ tailIndex 1 r.arity
  have he : join 1 r.arity x z=u := join_reconstruct 1 r.arity u
  have h := (annularChart_join_iff r j hp x z).mp (he.symm ▸ hu)
  have hall : ∀ i : Fin (1+r.arity), NonzeroRV (u i) →
      η⁻¹ ≤ codeValue (u i) ∧ codeValue (u i) ≤ η := by
    apply GammaBoundedProducts.all_coordinates 1 r.arity
      (fun t => NonzeroRV t → η⁻¹ ≤ codeValue t ∧ codeValue t ≤ η) u
    · intro l hl
      have hb := hβ x h.1 l hl
      exact ⟨(inv_le_inv_iff.mpr hβη).trans hb.1,hb.2.trans hβη⟩
    · intro l _
      fin_cases l
      have hl : η⁻¹ ≤ 1 := by simpa only [inv_one] using inv_le_inv_iff.mpr h1η
      exact ⟨hl.trans h.2.2.1.le,(h.2.2.2.trans (hΔ x h.1)).trans hΔη⟩
  exact hall i hi

def boundedAnnularChart (r : RVBoundedCharts.BoundedChart B k) (j : Fin r.arity)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j)) (Δ : Values.Gamma (M := M))
    (hΔ : ∀ x ∈ r.domain, codeValue (x j) ≤ Δ) : RVBoundedCharts.BoundedChart B (1+k) :=
  ⟨annularChart r.toChart j,annularChart_domain_bounded r.toChart j hp r.domain_bounded Δ hΔ⟩

end DiamondIntegral.Section4.VariableApertureRayCancellation
