import «section 4».GammaPushforwardCongruence
import «section 4».GammaConstantPushforward
import «section 4».GammaObjectPolynomial
import «section 4».GammaMeasuredProfileInvariance
import «section 4».GammaUnboundedSpecialization

/-! The actual profile and homogeneous polynomial of a weighted Gamma
singleton. This computes the finite Gamma coefficient used in balancing,
without an RV lift of either definable Gamma value. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaSingletonProfiles
open GammaDefinableEuler GammaOrderLogic GammaDefinableMaps GammaWeightProfiles
open GammaIndicators GammaIntegerFamilies GammaIteratedIntegral GammaPointFamilies
open GammaPushforwardCongruence GammaConstantPushforward GammaMeasuredProfileInvariance
open GammaNamesSubgroup GammaObjectPolynomial GammaPointAlgebra EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def productName (B : Base (M := M)) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) : additiveNames B :=
  ⟨toPaperGamma (α * β), GammaGroupNames.mul_definable_base B α β hα hβ⟩

theorem profile_singleton (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (k : EulerKind)
    (α β : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    (profile h00 hκ hs B hr hγ k {z : Fin 1 → Values.Gamma (M := M) | z 0 = α}
      (constant_definable (n := 0) B α hα) (fun _ => β) (constant_definable B β hβ)).val =
      point k (toPaperGamma (α * β)) := by
  let I : Set (Fin 1 → Values.Gamma (M := M)) := {z | z 0 = α}
  have hI : GammaDefinable B I := constant_definable (n := 0) B α hα
  let f := indicatorFamily B I hI
  have hμ : MapDefinable B (fun _ : Fin 1 → Values.Gamma (M := M) => β) := constant_definable B β hβ
  have hT := correctedWeight_graph B (fun _ => β) hμ
  have hc : GammaDefinableClosureAtBase B (α * β) := GammaGroupNames.mul_definable_base B α β hα hβ
  have hU : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | z 0 = (fun _ => α * β) (Fin.tail z)} :=
    constant_definable B (α * β) hc
  have hm (z : Fin 1 → Values.Gamma (M := M)) (hz : f.val z ≠ 0) :
      correctedWeight (fun _ => β) z = α * β := by
    have he : z 0 = α := by
      by_contra hn
      exact hz (by simp [f, indicatorFamily, I, hn])
    change β * (∏ i : Fin 1, z i) = α * β
    rw [Fin.prod_univ_one, he, mul_comm]
  have hp := pushforward_eq_on_support h00 hκ hs B hr hγ k
    (correctedWeight (fun _ => β)) (fun _ => α * β) hT hU f hm
  have hi : integrateAll h00 hκ hs B hr hγ k 1 f = 1 := by
    apply integrateAll_singleton h00 hκ hs B hr hγ k 1 f ![α] 1
    intro z
    have he : z = ![α] ↔ z 0 = α := by
      constructor
      · intro h
        exact congrFun h 0
      · intro h
        funext i
        fin_cases i
        exact h
    by_cases hz : z 0 = α <;> simp [f, indicatorFamily, I, he, hz]
  have hconst := pushforward_constant h00 hκ hs B hr hγ k (fun _ => α * β) hU (α * β) (fun _ => rfl) f
  rw [hi, one_zsmul] at hconst
  exact hp.trans hconst

theorem objectPolynomial_singleton (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (k : EulerKind)
    (α β : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    objectPolynomial h00 hκ hs B hr hγ k 1 {z : Fin 1 → Values.Gamma (M := M) | z 0 = α}
      (constant_definable (n := 0) B α hα) (fun _ => β) (constant_definable B β hβ) =
      GammaUnboundedSpecialization.pointMonomial B k 1 (productName B α β hα hβ) := by
  have hc : profileCoefficient h00 hκ hs B hr hγ k {z : Fin 1 → Values.Gamma (M := M) | z 0 = α}
      (constant_definable (n := 0) B α hα) (fun _ => β) (constant_definable B β hβ) =
      pointMonoidHom B k (Multiplicative.ofAdd (productName B α β hα hβ)) := by
    apply Subtype.ext
    exact profile_singleton h00 hκ hs B hr hγ k α β hα hβ
  apply Subtype.ext
  exact congrArg (Polynomial.monomial 1) hc

end DiamondIntegral.Section4.GammaSingletonProfiles
