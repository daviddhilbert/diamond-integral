import «section 6».OrderedStandardContractionLifts

/-! A proper label graft fixing every VF coordinate may be absorbed
into the first contraction stage. The resulting program is an actual
standard contraction on the original source in the same coordinate order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {B : DefSet (rawMixedSpace (M := M) (n+1) s) S}

def StandardContractionStage.precomposeFixedVF
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (T : StandardContractionStage (G := G) B) (g : Map A B) (hG : ProperCovariantHomeomorphism g)
    (hVF : ∀ p : A,(g p).val.1=p.val.1) (π : Fin r → Fin s) (hπ : Function.Injective π)
    (hRetain : ∀ p : A,∀ i,(g p).val.2 (π i)=p.val.2 i)
    (hUnit : ∀ p : A,HasMixedUnitDerivativeAt g p) : StandardContractionStage (G := G) A := by
  have hGeneric (p : A) (hInd : AlgebraicIndependent (vfParameterField S) p.val.1) :
      HasMixedUnitDerivativeAt (T.lift.comp g) p := by
    have hIndG : AlgebraicIndependent (vfParameterField S) (g p).val.1 := by rw [hVF p]; exact hInd
    exact (T.unitDerivative (g p)
      (not_mem_small_set_of_independent hc T.exceptional T.exceptional_dim (g p).val hIndG)).comp (hUnit p)
  let E := (exists_mixed_unit_derivative_exception hc hs hsmall (Nat.zero_lt_succ n) (T.lift.comp g) hGeneric).choose
  have hE := (exists_mixed_unit_derivative_exception hc hs hsmall (Nat.zero_lt_succ n) (T.lift.comp g) hGeneric).choose_spec
  exact {
    arity := T.arity
    target := T.target
    lift := T.lift.comp g
    home := lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ hG T.home
    proper := T.proper
    doublyBounded := T.doublyBounded
    relative := fun p i => (T.relative (g p) i).trans (congrFun (hVF p) i.castSucc)
    oldLabels := T.oldLabels ∘ π
    oldLabels_injective := T.oldLabels_injective.comp hπ
    retained := fun p i => (T.retained (g p) (π i)).trans (hRetain p i)
    leading := T.leading
    bundle := T.bundle
    exceptional := E
    exceptional_subset := hE.1
    exceptional_dim := hE.2.1
    unitDerivative := hE.2.2 }

variable {U : DefSet (rawMixedSpace (M := M) 0 q) S}

def OrderedStandardContractionProgram.precomposeFixedVF
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (T : OrderedStandardContractionProgram (G := G) S B U) (g : Map A B) (hG : ProperCovariantHomeomorphism g)
    (hVF : ∀ p : A,(g p).val.1=p.val.1) (π : Fin r → Fin s) (hπ : Function.Injective π)
    (hRetain : ∀ p : A,∀ i,(g p).val.2 (π i)=p.val.2 i)
    (hUnit : ∀ p : A,HasMixedUnitDerivativeAt g p) : OrderedStandardContractionProgram (G := G) S A U := by
  cases T with
  | step R tail =>
    exact .step (R.precomposeFixedVF h00 hc linear hκ hs hv hsmall hΓ g hG hVF π hπ hRetain hUnit) tail

theorem OrderedStandardContractionProgram.precomposeFixedVF_toMap
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (T : OrderedStandardContractionProgram (G := G) S B U) (g : Map A B) (hG : ProperCovariantHomeomorphism g)
    (hVF : ∀ p : A,(g p).val.1=p.val.1) (π : Fin r → Fin s) (hπ : Function.Injective π)
    (hRetain : ∀ p : A,∀ i,(g p).val.2 (π i)=p.val.2 i)
    (hUnit : ∀ p : A,HasMixedUnitDerivativeAt g p) :
    (T.precomposeFixedVF h00 hc linear hκ hs hv hsmall hΓ g hG hVF π hπ hRetain hUnit).toMap=T.toMap.comp g := by
  cases T with
  | step R tail => rfl

end DiamondIntegral.Section6
