import «section 4».GammaOrdinaryRing
import «section 4».GammaEulerEvaluation

/-! Numerical Euler evaluation on the actual Gamma category without
volume forms. Ordinary contracted bijections are handled by the proved
Gamma definable-bijection invariance. The map agrees on the whole measured
Gamma source with the existing evaluation that forgets weights. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryEulerEvaluation
open GammaOrdinaryCharts GammaOrderLogic GammaDefinableMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) {R : Type*} [CommRing R] (t : R)

def weightedEvaluation (k : EulerKind) : GammaRVChartPresentation.ChartRing B →+* R :=
  GammaEulerEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k t

def value (k : EulerKind) {n : ℕ} (a : Chart B n) : R :=
  weightedEvaluation h00 linear hκ hs B hr hγ hΓ t k (GammaRVChartPresentation.objectClass (toWeighted a))

theorem value_formula (k : EulerKind) {n : ℕ} (a : Chart B n) : value h00 linear hκ hs B hr hγ hΓ t k a =
    (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n (GammaIndicators.indicatorFamily B a.support a.support_definable) : R) * t ^ n :=
  GammaEulerEvaluation.evaluation_class h00 linear hκ hs B hr hγ hΓ k t (toWeighted a)

theorem value_ofWeighted (k : EulerKind) {n : ℕ} (a : GammaWeightedCharts.Chart B n) :
    value h00 linear hκ hs B hr hγ hΓ t k (ofWeighted a) =
      weightedEvaluation h00 linear hκ hs B hr hγ hΓ t k (GammaRVChartPresentation.objectClass a) := by
  rw [value_formula]
  exact (GammaEulerEvaluation.evaluation_class h00 linear hκ hs B hr hγ hΓ k t a).symm

def invariant (k : EulerKind) : GammaOrdinaryRing.Invariant B R where
  value _ a := value h00 linear hκ hs B hr hγ hΓ t k a
  unit := by
    have h := value_ofWeighted h00 linear hκ hs B hr hγ hΓ t k (GammaChartOperations.unit B)
    rw [GammaRVChartPresentation.class_unit, map_one] at h
    exact h
  product n m a b := by
    have h := value_ofWeighted h00 linear hκ hs B hr hγ hΓ t k
      (GammaChartOperations.product (toWeighted a) (toWeighted b))
    rw [GammaRVChartPresentation.class_product, map_mul] at h
    exact h
  iso n a b f := by
    rw [value_formula, value_formula]
    exact congrArg (fun z : ℤ => (z : R) * t ^ n)
      (GammaBijectiveRelations.integrateAll_bijOn h00 linear hκ hs B hr hγ hΓ k n n
        a.support a.support_definable b.support b.support_definable f.map f.graph_definable f.bijective)
  empty n a ha := by
    let e := GammaChartOperations.ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) (fun _ => 1)
      (constant_definable B 1 (GammaGroupNames.one_definable_base B))
    have he : GammaRVChartPresentation.objectClass (toWeighted a) = GammaRVChartPresentation.objectClass e :=
      GammaRVIdentityIso.class_eq_on_domain _ _ ha (fun _ _ => rfl)
    have h0 : GammaRVChartPresentation.objectClass e = 0 := GammaRVChartPresentation.class_empty B n (fun _ => 1)
      (constant_definable B 1 (GammaGroupNames.one_definable_base B))
    change weightedEvaluation h00 linear hκ hs B hr hγ hΓ t k (GammaRVChartPresentation.objectClass (toWeighted a)) = 0
    rw [he, h0, map_zero]
  scissor n a b c d h := by
    let hU := GammaQuantifierLogic.union_definable_base B _ _ a.support_definable b.support_definable
    let hN := GammaRelationLogic.inter_definable_base B _ _ a.support_definable b.support_definable
    let h1 : MapDefinable B (fun _ : Fin n → Values.Gamma (M := M) => 1) :=
      constant_definable B 1 (GammaGroupNames.one_definable_base B)
    have hc := GammaRVIdentityIso.class_eq_on_domain (toWeighted c)
      (GammaChartOperations.ofTotal B n (a.support ∪ b.support) hU (fun _ => 1) h1) h.1 (fun _ _ => rfl)
    have hd := GammaRVIdentityIso.class_eq_on_domain (toWeighted d)
      (GammaChartOperations.ofTotal B n (a.support ∩ b.support) hN (fun _ => 1) h1) h.2 (fun _ _ => rfl)
    change weightedEvaluation h00 linear hκ hs B hr hγ hΓ t k (GammaRVChartPresentation.objectClass (toWeighted c)) +
      weightedEvaluation h00 linear hκ hs B hr hγ hΓ t k (GammaRVChartPresentation.objectClass (toWeighted d)) = _
    rw [hc, hd]
    have hh := congrArg (weightedEvaluation h00 linear hκ hs B hr hγ hΓ t k)
      (GammaRVChartPresentation.class_scissor B n a.support b.support a.support_definable b.support_definable hU hN (fun _ => 1) h1)
    simp only [map_add] at hh
    exact hh

def evaluation (k : EulerKind) : GammaOrdinaryRing.Ring B →+* R :=
  GammaOrdinaryRing.lift B (invariant h00 linear hκ hs B hr hγ hΓ t k)

theorem evaluation_value (k : EulerKind) {n : ℕ} (a : Chart B n) :
    evaluation h00 linear hκ hs B hr hγ hΓ t k (GammaOrdinaryRing.objectClass a) = value h00 linear hκ hs B hr hγ hΓ t k a :=
  GammaOrdinaryRing.lift_class B (invariant h00 linear hκ hs B hr hγ hΓ t k) a

theorem evaluation_class (k : EulerKind) {n : ℕ} (a : Chart B n) :
    evaluation h00 linear hκ hs B hr hγ hΓ t k (GammaOrdinaryRing.objectClass a) =
      (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n (GammaIndicators.indicatorFamily B a.support a.support_definable) : R) * t ^ n :=
  (evaluation_value h00 linear hκ hs B hr hγ hΓ t k a).trans (value_formula h00 linear hκ hs B hr hγ hΓ t k a)

theorem evaluation_forget (k : EulerKind) :
    (evaluation h00 linear hκ hs B hr hγ hΓ t k).comp (GammaOrdinaryRing.forget B) = weightedEvaluation h00 linear hκ hs B hr hγ hΓ t k := by
  apply GammaRVChartPresentation.hom_ext B
  intro n a
  change evaluation h00 linear hκ hs B hr hγ hΓ t k (GammaOrdinaryRing.forget B (GammaRVChartPresentation.objectClass a)) = _
  rw [GammaOrdinaryRing.forget_class, evaluation_value]
  exact value_ofWeighted h00 linear hκ hs B hr hγ hΓ t k a

end DiamondIntegral.Section4.GammaOrdinaryEulerEvaluation
