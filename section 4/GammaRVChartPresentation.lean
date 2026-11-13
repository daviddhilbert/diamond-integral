import «section 4».GammaChartPresentation
import «section 4».GammaChartSpecializations

/-! A chart presentation retaining the manuscript's actual RV-contraction
condition on Gamma morphisms. The lift is a definable bijection between
full proper RV preimages over the original base, not a chosen RV section.
The map to the auxiliary all-bijections presentation and both profile
homomorphisms are constructed. Finite tagged unions and the graded
category identification are still separate obligations. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaRVChartPresentation
open GammaOrderLogic GammaDefinableMaps GammaWeightedCharts GammaChartOperations FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def codeValues {n : ℕ} (z : Fin n → M) : Fin n → Values.Gamma (M := M) :=
  fun i => codeValue (z i)

def sharp {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) : Set (Fin n → M) :=
  {z | Proper z ∧ codeValues z ∈ I}

theorem sharp_definable {B : Base (M := M)} {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) :
    DefinableOverBase B (fun _ : Fin n => .rv) (sharp I) := hI

def rawGraphOn {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M)))
    (F : (Fin n → M) → (Fin n → M)) : Set (Fin (n + n) → M) :=
  {w | w ∘ headIndex n n ∈ sharp I ∧ w ∘ tailIndex n n = F (w ∘ headIndex n n)}

structure RVVolumeIso {B : Base (M := M)} {n : ℕ} (a b : Chart B n) extends VolumeIso a b where
  lift : (Fin n → M) → (Fin n → M)
  lift_definable : DefinableOverBase B (fun _ : Fin (n + n) => .rv) (rawGraphOn a.support lift)
  lift_bijective : Set.BijOn lift (sharp a.support) (sharp b.support)
  contraction : ∀ z ∈ sharp a.support, codeValues (lift z) = map (codeValues z)

inductive Relation (B : Base (M := M)) : FreeCommRing (GammaChartPresentation.Generator B) → Prop where
  | unit : Relation B (GammaChartPresentation.symbol (GammaChartOperations.unit B) - 1)
  | product {n m : ℕ} (a : Chart B m) (b : Chart B n) :
      Relation B (GammaChartPresentation.symbol (GammaChartOperations.product a b) -
        GammaChartPresentation.symbol a * GammaChartPresentation.symbol b)
  | iso {n : ℕ} (a b : Chart B n) (F : RVVolumeIso a b) :
      Relation B (GammaChartPresentation.symbol a - GammaChartPresentation.symbol b)
  | empty (n : ℕ) (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hμ : MapDefinable B μ) :
      Relation B (GammaChartPresentation.symbol
        (ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) μ hμ))
  | scissor (n : ℕ) (I J : Set (Fin n → Values.Gamma (M := M)))
      (hI : GammaDefinable B I) (hJ : GammaDefinable B J)
      (hU : GammaDefinable B (I ∪ J)) (hN : GammaDefinable B (I ∩ J))
      (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
      Relation B (GammaChartPresentation.symbol (ofTotal B n (I ∪ J) hU μ hμ) +
        GammaChartPresentation.symbol (ofTotal B n (I ∩ J) hN μ hμ) -
        GammaChartPresentation.symbol (ofTotal B n I hI μ hμ) -
        GammaChartPresentation.symbol (ofTotal B n J hJ μ hμ))

theorem relation_forget (B : Base (M := M)) (r : FreeCommRing (GammaChartPresentation.Generator B))
    (h : Relation B r) : GammaChartPresentation.Relation B r := by
  cases h with
  | unit => exact .unit
  | product a b => exact .product a b
  | iso a b F => exact .iso a b F.toVolumeIso
  | empty n μ hμ => exact .empty n μ hμ
  | scissor n I J hI hJ hU hN μ hμ => exact .scissor n I J hI hJ hU hN μ hμ

def relationIdeal (B : Base (M := M)) : Ideal (FreeCommRing (GammaChartPresentation.Generator B)) :=
  Ideal.span {r | Relation B r}

theorem relationIdeal_le (B : Base (M := M)) : relationIdeal B ≤ GammaChartPresentation.relationIdeal B := by
  apply Ideal.span_le.mpr
  intro r hr
  exact Ideal.subset_span (relation_forget B r hr)

def ChartRing (B : Base (M := M)) := FreeCommRing (GammaChartPresentation.Generator B) ⧸ relationIdeal B
  deriving CommRing

def forget (B : Base (M := M)) : ChartRing B →+* GammaChartPresentation.ChartRing B :=
  Ideal.Quotient.factor (relationIdeal_le B)

theorem forget_symbol (B : Base (M := M)) {n : ℕ} (a : Chart B n) :
    forget B (Ideal.Quotient.mk (relationIdeal B) (GammaChartPresentation.symbol a)) =
      Ideal.Quotient.mk (GammaChartPresentation.relationIdeal B) (GammaChartPresentation.symbol a) := rfl

theorem forget_surjective (B : Base (M := M)) : Function.Surjective (forget B) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (relationIdeal B) p, rfl⟩

def interpretation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    ChartRing B →+* GammaFunctionPolynomial.sourceRing B k :=
  (GammaChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ k).comp (forget B)

theorem interpretation_symbol (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ} (a : Chart B n) :
    interpretation h00 linear hκ hs B hr hγ hΓ k
      (Ideal.Quotient.mk (relationIdeal B) (GammaChartPresentation.symbol a)) =
      chartPolynomial h00 hκ hs B hr hγ k a :=
  GammaChartPresentation.interpretation_symbol h00 linear hκ hs B hr hγ hΓ k a

def specialize (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    {R : Type*} [CommRing R] (u : Multiplicative (GammaNamesSubgroup.additiveNames B) →* R) (T : R) :
    ChartRing B →+* R :=
  (GammaUnboundedSpecialization.specialize B k u T).comp (interpretation h00 linear hκ hs B hr hγ hΓ k)

end DiamondIntegral.Section4.GammaRVChartPresentation
