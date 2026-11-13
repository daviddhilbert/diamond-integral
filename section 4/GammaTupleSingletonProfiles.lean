import «section 4».GammaFiniteNames
import «section 4».GammaSingletonProfiles

/-! Actual weighted Gamma singleton profiles in every finite arity,
including degree zero. Only Gamma names are used, without RV lifts. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaTupleSingletonProfiles
open GammaDefinableEuler GammaOrderLogic GammaDefinableMaps GammaWeightProfiles
open GammaIndicators GammaIntegerFamilies GammaIteratedIntegral GammaPointFamilies
open GammaPushforwardCongruence GammaConstantPushforward GammaNamesSubgroup
open GammaMeasuredProfileInvariance
open GammaObjectPolynomial GammaPointAlgebra EulerFunction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem singleton_definable (B : Base (M := M)) {n : ℕ} (α : Fin n → Values.Gamma (M := M))
    (hα : ∀ i, GammaDefinableClosureAtBase B (α i)) : GammaDefinable B ({α} : Set (Fin n → Values.Gamma (M := M))) := by
  let R (i : Fin n) : Set (Fin n → Values.Gamma (M := M)) := {z | z i = α i}
  have hR (i : Fin n) : GammaDefinable B (R i) :=
    GammaRelationLogic.preimage_definable_base B _ (constant_definable (n := 0) B (α i) (hα i)) (fun _ => i)
  have h := GammaQuantifierLogic.finite_iInter_definable_base B R hR
  convert h using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_iInter, R, Set.mem_ofPred_eq, funext_iff]

def productName (B : Base (M := M)) {n : ℕ} (α : Fin n → Values.Gamma (M := M))
    (β : Values.Gamma (M := M)) (hα : ∀ i, GammaDefinableClosureAtBase B (α i))
    (hβ : GammaDefinableClosureAtBase B β) : additiveNames B :=
  ⟨toPaperGamma (β * ∏ i, α i), GammaGroupNames.mul_definable_base B β _ hβ
    ((namesSubgroup B).toSubmonoid.prod_mem (fun i _ => hα i))⟩

theorem profile_singleton (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (k : EulerKind)
    {n : ℕ} (α : Fin n → Values.Gamma (M := M)) (β : Values.Gamma (M := M))
    (hα : ∀ i, GammaDefinableClosureAtBase B (α i)) (hβ : GammaDefinableClosureAtBase B β) :
    (profile h00 hκ hs B hr hγ k {α} (singleton_definable B α hα) (fun _ => β)
      (constant_definable B β hβ)).val = point k (toPaperGamma (β * ∏ i, α i)) := by
  let f := indicatorFamily B ({α} : Set (Fin n → Values.Gamma (M := M))) (singleton_definable B α hα)
  have hμ : MapDefinable B (fun _ : Fin n → Values.Gamma (M := M) => β) := constant_definable B β hβ
  have hT := correctedWeight_graph B (fun _ => β) hμ
  have hU : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = (fun _ => β * ∏ i, α i) (Fin.tail z)} :=
    constant_definable B _ (productName B α β hα hβ).property
  have hm (z : Fin n → Values.Gamma (M := M)) (hz : f.val z ≠ 0) :
      correctedWeight (fun _ => β) z = β * ∏ i, α i := by
    have he : z = α := by
      by_contra hn
      exact hz (by simp [f, indicatorFamily, hn])
    subst z
    rfl
  have hp := pushforward_eq_on_support h00 hκ hs B hr hγ k
    (correctedWeight (fun _ => β)) (fun _ => β * ∏ i, α i) hT hU f hm
  have hi : integrateAll h00 hκ hs B hr hγ k n f = 1 := by
    apply integrateAll_singleton h00 hκ hs B hr hγ k n f α 1
    intro z
    by_cases hz : z = α <;> simp [f, indicatorFamily, hz]
  have hc := pushforward_constant h00 hκ hs B hr hγ k (fun _ => β * ∏ i, α i) hU
    (β * ∏ i, α i) (fun _ => rfl) f
  rw [hi, one_zsmul] at hc
  exact hp.trans hc

theorem objectPolynomial_singleton (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (k : EulerKind)
    {n : ℕ} (α : Fin n → Values.Gamma (M := M)) (β : Values.Gamma (M := M))
    (hα : ∀ i, GammaDefinableClosureAtBase B (α i)) (hβ : GammaDefinableClosureAtBase B β) :
    objectPolynomial h00 hκ hs B hr hγ k n {α} (singleton_definable B α hα) (fun _ => β)
      (constant_definable B β hβ) = GammaUnboundedSpecialization.pointMonomial B k n (productName B α β hα hβ) := by
  have hc : profileCoefficient h00 hκ hs B hr hγ k {α} (singleton_definable B α hα)
      (fun _ => β) (constant_definable B β hβ) =
      pointMonoidHom B k (Multiplicative.ofAdd (productName B α β hα hβ)) := by
    apply Subtype.ext
    exact profile_singleton h00 hκ hs B hr hγ k α β hα hβ
  apply Subtype.ext
  exact congrArg (Polynomial.monomial n) hc

end DiamondIntegral.Section4.GammaTupleSingletonProfiles
