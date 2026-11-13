import «section 4».IntrinsicBalancedRadiusQuotient

/-! Forgetting volume forms and passing to ordinary RES fibres are
surjective. Hence the actual intrinsic bounded tensor evaluation and its
source-radius quotient evaluation are surjective, without a claim about
the RV comparison kernel. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RESOrdinarySurjectivity
open IntrinsicFiniteGammaAlgebras
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem forget_surjective (B : Base (M := M)) : Function.Surjective (RESOrdinaryRing.forget B) := by
  have hc : (RESOrdinaryRing.forget B).comp (Ideal.Quotient.mk (RESChartRing.relationIdeal B)) =
      Ideal.Quotient.mk (RESOrdinaryRing.relationIdeal B) := by
    apply FreeCommRing.hom_ext
    intro a
    exact RESOrdinaryRing.forget_objectClass B a.2
  intro y
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk (RESChartRing.relationIdeal B) r, (RingHom.congr_fun hc r).trans hr⟩

theorem reducedForget_surjective (B : Base (M := M)) : Function.Surjective (RESOrdinaryReduction.forget B) := by
  intro y
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := forget_surjective B r
  exact ⟨x, (congrArg (RESOrdinaryReduction.quotient B) hx).trans hr⟩

theorem intrinsicLeft_surjective (B : Base (M := M)) : Function.Surjective (IntrinsicBalancedEvaluations.ordinaryLeft B) := by
  intro y
  obtain ⟨x, hx⟩ := reducedForget_surjective B (RESDisjointReduction.Ordinary.equivalence B y)
  refine ⟨(RESDisjointPresentation.equivalence B).symm x, ?_⟩
  change (RESDisjointReduction.Ordinary.equivalence B).symm
    (RESOrdinaryReduction.forget B ((RESDisjointPresentation.equivalence B) ((RESDisjointPresentation.equivalence B).symm x))) = y
  rw [RingEquiv.apply_symm_apply, hx, RingEquiv.symm_apply_apply]

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem tensor_evaluation_surjective (k : EulerKind) : Function.Surjective (IntrinsicBalancedEvaluations.bounded h00 linear hκ hs B hr hγ hΓ k) := by
  intro y
  obtain ⟨x, hx⟩ := intrinsicLeft_surjective B y
  exact ⟨x ⊗ₜ[Coeff B] 1, (IntrinsicBalancedEvaluations.bounded_on_res h00 linear hκ hs B hr hγ hΓ k x).trans hx⟩

theorem radius_evaluation_surjective (k : EulerKind) : Function.Surjective (IntrinsicBalancedRadiusQuotient.evaluation h00 linear hκ hs B hr hγ hΓ k) := by
  intro y
  obtain ⟨x, hx⟩ := intrinsicLeft_surjective B y
  exact ⟨IntrinsicBalancedRadiusQuotient.quotient B (x ⊗ₜ[Coeff B] 1),
    (IntrinsicBalancedRadiusQuotient.evaluation_res h00 linear hκ hs B hr hγ hΓ k x).trans hx⟩

end DiamondIntegral.Section4.RESOrdinarySurjectivity
