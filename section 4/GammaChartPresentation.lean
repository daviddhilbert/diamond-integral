import «section 4».GammaChartOperations
import Mathlib.RingTheory.FreeCommRing
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! An explicit ring presentation of actual weighted Gamma charts, using
all volume-preserving definable bijections. Both proved Euler profiles
descend to this presentation. Identification with the manuscript category,
whose morphisms also require RV lifts, is a separate obligation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaChartPresentation
open GammaOrderLogic GammaDefinableMaps GammaWeightedCharts GammaChartOperations
open GammaObjectRelations GammaObjectPolynomial

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Generator (B : Base (M := M)) := Σ n, Chart B n

def symbol {B : Base (M := M)} {n : ℕ} (a : Chart B n) : FreeCommRing (Generator B) := FreeCommRing.of ⟨n, a⟩

inductive Relation (B : Base (M := M)) : FreeCommRing (Generator B) → Prop where
  | unit : Relation B (symbol (GammaChartOperations.unit B) - 1)
  | product {n m : ℕ} (a : Chart B m) (b : Chart B n) :
      Relation B (symbol (GammaChartOperations.product a b) - symbol a * symbol b)
  | iso {n : ℕ} (a b : Chart B n) (F : VolumeIso a b) : Relation B (symbol a - symbol b)
  | empty (n : ℕ) (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hμ : MapDefinable B μ) :
      Relation B (symbol (ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) μ hμ))
  | scissor (n : ℕ) (I J : Set (Fin n → Values.Gamma (M := M)))
      (hI : GammaDefinable B I) (hJ : GammaDefinable B J)
      (hU : GammaDefinable B (I ∪ J)) (hN : GammaDefinable B (I ∩ J))
      (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
      Relation B (symbol (ofTotal B n (I ∪ J) hU μ hμ) + symbol (ofTotal B n (I ∩ J) hN μ hμ) -
        symbol (ofTotal B n I hI μ hμ) - symbol (ofTotal B n J hJ μ hμ))

def relationIdeal (B : Base (M := M)) : Ideal (FreeCommRing (Generator B)) := Ideal.span {r | Relation B r}

def ChartRing (B : Base (M := M)) := FreeCommRing (Generator B) ⧸ relationIdeal B
  deriving CommRing

def freeInterpretation (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) : FreeCommRing (Generator B) →+* GammaFunctionPolynomial.sourceRing B k :=
  FreeCommRing.lift (fun a => chartPolynomial h00 hκ hs B hr hγ k a.2)

theorem freeInterpretation_symbol (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (a : Chart B n) :
    freeInterpretation h00 hκ hs B hr hγ k (symbol a) = chartPolynomial h00 hκ hs B hr hγ k a :=
  FreeCommRing.lift_of _ _

theorem relation_vanishes (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (r : FreeCommRing (Generator B)) (hrel : Relation B r) : freeInterpretation h00 hκ hs B hr hγ k r = 0 := by
  cases hrel with
  | unit =>
    rw [map_sub, map_one, freeInterpretation_symbol, chartPolynomial_unit, sub_self]
  | product a b =>
    rw [map_sub, map_mul, freeInterpretation_symbol, freeInterpretation_symbol, freeInterpretation_symbol,
      chartPolynomial_product h00 linear hκ hs B hr hγ hΓ k, sub_self]
  | iso a b F =>
    rw [map_sub, freeInterpretation_symbol, freeInterpretation_symbol]
    exact sub_eq_zero.mpr (chartPolynomial_volumeIso h00 linear hκ hs B hr hγ hΓ k a b F)
  | empty n μ hμ =>
    rw [freeInterpretation_symbol, chartPolynomial_ofTotal]
    exact objectPolynomial_empty h00 hκ hs B hr hγ k n _ μ hμ
  | scissor n I J hI hJ hU hN μ hμ =>
    simp only [map_sub, map_add, freeInterpretation_symbol, chartPolynomial_ofTotal]
    rw [sub_sub]
    exact sub_eq_zero.mpr (objectPolynomial_scissor h00 hκ hs B hr hγ k n I J hI hJ hU hN μ hμ)

theorem relationIdeal_vanishes (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    relationIdeal B ≤ RingHom.ker (freeInterpretation h00 hκ hs B hr hγ k) := by
  apply Ideal.span_le.mpr
  intro r hrR
  exact relation_vanishes h00 linear hκ hs B hr hγ hΓ k r hrR

def interpretation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    ChartRing B →+* GammaFunctionPolynomial.sourceRing B k :=
  Ideal.Quotient.lift (relationIdeal B) (freeInterpretation h00 hκ hs B hr hγ k)
    (fun _ hrR => relationIdeal_vanishes h00 linear hκ hs B hr hγ hΓ k hrR)

theorem interpretation_symbol (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ} (a : Chart B n) :
    interpretation h00 linear hκ hs B hr hγ hΓ k (Ideal.Quotient.mk (relationIdeal B) (symbol a)) =
      chartPolynomial h00 hκ hs B hr hγ k a :=
  freeInterpretation_symbol h00 hκ hs B hr hγ k a

end DiamondIntegral.Section4.GammaChartPresentation
