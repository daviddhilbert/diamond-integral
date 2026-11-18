import «section 6».AllDimensionalOrderedContractions
import «section 6».BinaryContractionsAnyOrder
import «section 6».BinaryFieldBase
import «section 6».BinaryMeasuredExistence
import «section 6».BinaryMeasuredExistenceFieldBase
import «section 6».BinaryOrderedContractions
import «section 6».BinaryProperPreparation
import «section 6».BinaryStandardContractionExistence
import «section 6».BoundedVariableUnaryMatching
import «section 6».ClosedSourceImageBounds
import «section 6».DiamondLiftHomomorphism
import «section 6».DiamondSimultaneous
import «section 6».DiamondSpecialIsomorphisms
import «section 6».DiamondStandardContraction
import «section 6».FiniteImageMeasuredExistence
import «section 6».FiniteImageMeasuredFieldBase
import «section 6».FiniteMeasuredVFChainLifting
import «section 6».GammaBounds
import «section 6».GammaFormBounds
import «section 6».MeasuredExistence
import «section 6».MeasuredExistenceFieldBase
import «section 6».MeasuredMorphismsLiftChains
import «section 6».PreparationFieldBase
import «section 6».ProperComposition
import «section 6».ProperHomeomorphisms
import «section 6».ProperMeasuredRVLifts
import «section 6».ProperPreparation
import «section 6».RelativeApertureChains
import «section 6».Remark620
import «section 6».SpecialCovariant
import «section 6».StandardContractionExistence
import «section 6».UnaryFieldBase
import «section 6».UnaryMeasuredExistence
import «section 6».UnaryMeasuredExistenceFieldBase
import «section 6».UnaryProperPreparation
import «section 6».UnaryRelationContraction
import «section 6».UnaryStandardContraction
import «section 5».GammaQEFiniteLaws

/-! The numbered Section 6 statements without the unary Γ rational-affine
input. That input is the theorem
`Section5.GammaQE.gamma_piecewise_rational_affine`, proved from RV quantifier
elimination with no further hypotheses. Each `_discharged` statement is the
original one with that argument removed (and, where the original statement
mentions it, instantiated by that theorem). -/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section DischargedAll

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_27_doublyBounded` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_27_doublyBounded_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) :
    ∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
      ∃ T : OrderedStandardContractionProgram (G := G) S A U,Nonempty (OrderedStandardContractionLift T)  := by
  apply lemma_6_27_doublyBounded (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_27_normalized` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_27_normalized_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier) (e : Equiv.Perm (Fin n)) :
    ∃ D : ZeroCenteredData A,∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
      ∃ T : OrderedStandardContractionProgram (G := G) S (reindexedVFSet D.map.image e) U,
        Nonempty (OrderedStandardContractionLift T)  := by
  apply lemma_6_27_normalized (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_27_binary_normalized` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_27_binary_normalized_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (e : Equiv.Perm (Fin 2)) :
    ∃ D : ZeroCenteredData A,∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
      ∃ T : OrderedStandardContractionProgram (G := G) S (reindexedVFSet D.map.image e) U,
        Nonempty (OrderedStandardContractionLift T)  := by
  apply lemma_6_27_binary_normalized (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_19_binary_vfGenerated` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_19_binary_vfGenerated_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) (S : Set M))
    (hA : ProperInvariant (S : Set M) A.carrier) (hARV : IsRVPullback A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 2 r) (S : Set M))
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant (S : Set M) (C i).carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 2 s) (S : Set M), ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant (S : Set M) B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
        IsRVPullback (f.restrict (hCA i)).image.carrier  := by
  apply lemma_6_19_binary_vfGenerated (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ} {S : Set M}

/-- `lemma_6_21_binary` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_21_binary_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S) (hCA : ∀ i, (C i).carrier ⊆ A.carrier)
    (hC : ∀ i, ProperInvariant S (C i).carrier) (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier)
    (ω : Mixed M 2 r → Gamma M) (hGraph : S.Definable LRV (mixedGammaGraph A.carrier ω))
    (hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ}) :
    ∃ T : MeasuredCoordinatePreparation (G := G) A C hCA (gammaFormMap A ω hGraph),
      ∀ i, (∀ a : Fin 2 → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ (C i).carrier}.Finite) →
      ∃ L : MeasuredRVLiftData (G := G) (C i) ((gammaFormMap A ω hGraph).comp (Map.inclusion (hCA i))),
        L.object.arity = T.arity ∧ ∀ p : C i, HEq (L.map p).val (T.map ⟨p.val,hCA i p.property⟩).val  := by
  apply lemma_6_21_binary (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ}

/-- `lemma_6_21_binary_vfGenerated` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_21_binary_vfGenerated_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) (S : Set M))
    (C : Fin k → DefSet (rawMixedSpace (M := M) 2 r) (S : Set M))
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant (S : Set M) (C i).carrier)
    (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier)
    (ω : Mixed M 2 r → Gamma M) (hGraph : (S : Set M).Definable LRV (mixedGammaGraph A.carrier ω))
    (hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ}) :
    ∃ T : MeasuredCoordinatePreparation (G := G) A C hCA (gammaFormMap A ω hGraph),
      ∀ i, (∀ a : Fin 2 → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ (C i).carrier}.Finite) →
      ∃ L : MeasuredRVLiftData (G := G) (C i) ((gammaFormMap A ω hGraph).comp (Map.inclusion (hCA i))),
        L.object.arity = T.arity ∧ ∀ p : C i, HEq (L.map p).val (T.map ⟨p.val,hCA i p.property⟩).val  := by
  apply lemma_6_21_binary_vfGenerated (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_27_binary_doublyBounded` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_27_binary_doublyBounded_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier) :
    ∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
      ∃ T : OrderedStandardContractionProgram (G := G) S A U,Nonempty (OrderedStandardContractionLift T)  := by
  apply lemma_6_27_binary_doublyBounded (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_19_binary` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_19_binary_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S)
    (hA : ProperInvariant S A.carrier) (hARV : IsRVPullback A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 2 s) S, ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
        IsRVPullback (f.restrict (hCA i)).image.carrier  := by
  apply lemma_6_19_binary (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_27_binary` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_27_binary_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (e : Equiv.Perm (Fin 2)) : Nonempty (BinaryStandardContraction (G := G) A e)  := by
  apply lemma_6_27_binary (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
open CategoryTheory
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_38_bounded_variable_apertures` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_38_bounded_variable_apertures_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field,x≠0 ∧ Valued.v x.val≠1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (B : DefSet (rawMixedSpace (M := M) 1 s) (S : Set M))
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant (S : Set M) A.carrier) (hB : ProperInvariant (S : Set M) B.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (hωLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ})
    (hσLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ B.carrier ∧ gammaFormExtension σ (a,u)=γ})
    (hGeneric : ∀ a : A,AlgebraicIndependent (vfParameterField (S : Set M)) a.val.1 →
      ∃ J : VF M,HasMixedVFJacobianAt f a J ∧ vfValue J=(gammaMapValue ω a/gammaMapValue σ (f a)).val) :
    ∃ H : UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ,
      RelativeApertureChain (G := G) A H.geometry.source H.geometry.sourceMap ∧
      RelativeApertureChain (G := G) B H.geometry.target H.geometry.targetMap  := by
  apply lemma_6_38_bounded_variable_apertures (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
open CategoryTheory
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_38_bounded_variable_apertures_contractible` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_38_bounded_variable_apertures_contractible_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field,x≠0 ∧ Valued.v x.val≠1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (B : DefSet (rawMixedSpace (M := M) 1 s) (S : Set M))
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant (S : Set M) A.carrier) (hB : ProperInvariant (S : Set M) B.carrier)
    (hFinite : ∀ a : Fin 1 → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (hωLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ})
    (hσLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ B.carrier ∧ gammaFormExtension σ (a,u)=γ})
    (hGeneric : ∀ a : A,AlgebraicIndependent (vfParameterField (S : Set M)) a.val.1 →
      ∃ J : VF M,HasMixedVFJacobianAt f a J ∧ vfValue J=(gammaMapValue ω a/gammaMapValue σ (f a)).val) :
    ∃ H : UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ,
      RelativeApertureChain (G := G) A H.geometry.source H.geometry.sourceMap ∧
      RelativeApertureChain (G := G) B H.geometry.target H.geometry.targetMap ∧
      (∀ p ∈ H.geometry.source.carrier,∀ q ∈ H.geometry.source.carrier,p.2=q.2 →
        gammaFormExtension (H.geometry.sourceForm h00 ω) p=gammaFormExtension (H.geometry.sourceForm h00 ω) q) ∧
      (∀ p ∈ H.geometry.target.carrier,∀ q ∈ H.geometry.target.carrier,p.2=q.2 →
        gammaFormExtension (H.geometry.targetForm h00 σ) p=gammaFormExtension (H.geometry.targetForm h00 σ) q) ∧
      ∃ (hA' : ∀ a : Fin 1 → VF M,{u : Fin H.geometry.sourceArity → RVInfinity M |
            (a,u) ∈ H.geometry.source.carrier}.Finite)
        (hB' : ∀ b : Fin 1 → VF M,{v : Fin H.geometry.targetArity → RVInfinity M |
            (b,v) ∈ H.geometry.target.carrier}.Finite),
        (H.sourceRV hA').doublyBounded ∧ (H.targetRV hB').doublyBounded ∧
        (∀ u,(H.sourceRV hA').object.value u=fun _ => u.val H.sourceIndex) ∧
        (∀ v,(H.targetRV hB').object.value v=fun _ => v.val H.targetIndex) ∧
        ∃ e : MeasuredRVIso (H.sourceRV hA') (H.targetRV hB'),
          ∀ p : H.geometry.source,
            e.iso.hom.map (pureRVTagQuotient H.geometry.source p)=
              pureRVTagQuotient H.geometry.target (H.geometry.map p)  := by
  apply lemma_6_38_bounded_variable_apertures_contractible (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

/-- `remark_6_4` with the unary Γ rational-affine input discharged. -/
theorem remark_6_4_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hVF : VFBounded A.carrier) (hRV : RVSupportDoublyBounded A.carrier)
    (hclosed : ∀ u, IsClosed (vfFibre A.carrier u)) (hradii : CovariantRadii f)
    (hNZ : ∀ p : A, ∀ i, ((f p).val.2 i).val ≠ iRVZero) :
    RVSupportDoublyBounded (mixedMapRange f)  := by
  apply remark_6_4 (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

/-- `remark_6_4_properCovariant` with the unary Γ rational-affine input discharged. -/
theorem remark_6_4_properCovariant_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hVF : VFBounded A.carrier) (hRV : RVSupportDoublyBounded A.carrier)
    (himage : VFBounded (mixedMapRange f))
    (hclosed : ∀ u, IsClosed (vfFibre A.carrier u)) (hradii : CovariantRadii f)
    (hNZ : ∀ p : A, ∀ i, ((f p).val.2 i).val ≠ iRVZero) : ProperCovariant f  := by
  apply remark_6_4_properCovariant (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGrothendieck DiamondIntegral.Section6.DiamondLift
open DiamondIntegral.Section6.DiamondEmpty DiamondIntegral.Section6.DiamondSurjectivity
namespace DiamondIntegral.Section6.DiamondLiftHomomorphism
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_33_diamond` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_33_diamond_discharged (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (B₀ : VFGeneratedFieldBase T) (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {U V : MeasuredRVObject (M := M) (T : Set M) k} (e : MeasuredRVIso U V)
    (hUd : U.doublyBounded) (hVd : V.doublyBounded)
    (hU : ProperInvariant (T : Set M) (rvLift U.object).carrier)
    (hV : ProperInvariant (T : Set M) (rvLift V.object).carrier) :
    ∃ F : Morphism G (liftObject U hU) (liftObject V hV),
      ∀ p, e.iso.hom.map.graph p.val.2 (F.map p).val.2  := by
  apply lemma_6_33_diamond (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6.DiamondLiftHomomorphism
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondGroupoid
namespace DiamondIntegral.Section6.DiamondSimultaneous
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_38_diamond` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_38_diamond_discharged (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (B₀ : VFGeneratedFieldBase T) (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {A B : VFObject (M := M) (T : Set M) 1} (F : Morphism G A B) :
    ∃ H : UnaryRelativeMeasuredMatching (G := G) A.carrier B.carrier F.map h00 A.form B.form,
      RelativeApertureChain (G := G) A.carrier H.geometry.source H.geometry.sourceMap ∧
      RelativeApertureChain (G := G) B.carrier H.geometry.target H.geometry.targetMap  := by
  apply lemma_6_38_diamond (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6.DiamondSimultaneous
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondGroupoid
namespace DiamondIntegral.Section6.DiamondSimultaneous
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_38_diamond_contractible` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_38_diamond_contractible_discharged (h00 : M ⊨ Axioms.ACVF00)
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (B₀ : VFGeneratedFieldBase T) (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {A B : VFObject (M := M) (T : Set M) 1} (F : Morphism G A B) :
    ∃ H : UnaryRelativeMeasuredMatching (G := G) A.carrier B.carrier F.map h00 A.form B.form,
      RelativeApertureChain (G := G) A.carrier H.geometry.source H.geometry.sourceMap ∧
      RelativeApertureChain (G := G) B.carrier H.geometry.target H.geometry.targetMap ∧
      (∀ p ∈ H.geometry.source.carrier, ∀ q ∈ H.geometry.source.carrier, p.2 = q.2 →
        gammaFormExtension (H.geometry.sourceForm h00 A.form) p =
          gammaFormExtension (H.geometry.sourceForm h00 A.form) q) ∧
      (∀ p ∈ H.geometry.target.carrier, ∀ q ∈ H.geometry.target.carrier, p.2 = q.2 →
        gammaFormExtension (H.geometry.targetForm h00 B.form) p =
          gammaFormExtension (H.geometry.targetForm h00 B.form) q) ∧
      ∃ (hA' : ∀ a : Fin 1 → VF M, {u : Fin H.geometry.sourceArity → RVInfinity M |
            (a, u) ∈ H.geometry.source.carrier}.Finite)
        (hB' : ∀ b : Fin 1 → VF M, {v : Fin H.geometry.targetArity → RVInfinity M |
            (b, v) ∈ H.geometry.target.carrier}.Finite),
        (H.sourceRV hA').doublyBounded ∧ (H.targetRV hB').doublyBounded ∧
        (∀ u, (H.sourceRV hA').object.value u = fun _ => u.val H.sourceIndex) ∧
        (∀ v, (H.targetRV hB').object.value v = fun _ => v.val H.targetIndex) ∧
        ∃ e : MeasuredRVIso (H.sourceRV hA') (H.targetRV hB'),
          ∀ p : H.geometry.source,
            e.iso.hom.map (pureRVTagQuotient H.geometry.source p) =
              pureRVTagQuotient H.geometry.target (H.geometry.map p)  := by
  apply lemma_6_38_diamond_contractible (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6.DiamondSimultaneous
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGroupoid DiamondIntegral.Section6.DiamondSurjectivity
namespace DiamondIntegral.Section6.DiamondSpecialIsomorphisms
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `remark_6_15` with the unary Γ rational-affine input discharged. -/
theorem remark_6_15_discharged (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    {A B : VFObject (M := M) S n} (F : Map A.carrier B.carrier)
    (H : RelativeApertureChain (G := G) A.carrier B.carrier F)
    (E : DefSet (rawMixedSpace (M := M) n A.labels) S)
    (hE : vfDim (rawRVSpace (M := M) 1) E < n ∨ E.carrier = ∅)
    (hform : ∀ p : A.carrier, p.val ∉ E.carrier → gammaMapValue A.form p = gammaMapValue B.form (F p)) :
    Nonempty (Morphism G A B)  := by
  apply remark_6_15 (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6.DiamondSpecialIsomorphisms
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondLift DiamondIntegral.Section6.DiamondSurjectivity
namespace DiamondIntegral.Section6.DiamondStandardContraction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `remark_6_28` with the unary Γ rational-affine input discharged. -/
theorem remark_6_28_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : VFObject (M := M) S (n+1)) {e : Equiv.Perm (Fin (n+1))}
    (F : NormalizedMeasuredContraction (G := G) A.carrier A.form e) (k : ℕ) (π : Fin k → Fin A.labels) :
    ∃ hP, Isomorphic G (headStartSourceObject h00 hc hκ hs hv A k π)
      (liftObject (F.headStartMeasuredObject h00 hc (Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) hκ hs hv hsmall hΓ k π (object_hFin A π)) hP)  := by
  apply remark_6_28 (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6.DiamondStandardContraction
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondLift DiamondIntegral.Section6.DiamondSurjectivity
namespace DiamondIntegral.Section6.DiamondStandardContraction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `remark_6_28_exists` with the unary Γ rational-affine input discharged. -/
theorem remark_6_28_exists_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : VFObject (M := M) S (n+1)) (e : Equiv.Perm (Fin (n+1))) :
    Nonempty (NormalizedMeasuredContraction (G := G) A.carrier A.form e)  := by
  apply remark_6_28_exists (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6.DiamondStandardContraction
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n r k : ℕ} {S : Set M}

/-- `lemma_6_21_finite_image` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_21_finite_image_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S) (hCA : ∀ i, (C i).carrier ⊆ A.carrier)
    (hC : ∀ i, ProperInvariant S (C i).carrier) (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier)
    (ω : Mixed M (n+1) r → Gamma M) (hGraph : S.Definable LRV (mixedGammaGraph A.carrier ω))
    (hFinite : (gammaFormMap A ω hGraph).image.carrier.Finite)
    (hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ}) :
    ∃ T : MeasuredCoordinatePreparation (G := G) A C hCA (gammaFormMap A ω hGraph),
      ∀ i, (∀ a : Fin (n+1) → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ (C i).carrier}.Finite) →
      ∃ L : MeasuredRVLiftData (G := G) (C i) ((gammaFormMap A ω hGraph).comp (Map.inclusion (hCA i))),
        L.object.arity = T.arity ∧ ∀ p : C i, HEq (L.map p).val (T.map ⟨p.val,hCA i p.property⟩).val  := by
  apply lemma_6_21_finite_image (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n r k : ℕ}

/-- `lemma_6_21_finite_image_vfGenerated` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_21_finite_image_vfGenerated_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) (S : Set M))
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) (S : Set M))
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant (S : Set M) (C i).carrier)
    (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier)
    (ω : Mixed M (n+1) r → Gamma M) (hGraph : (S : Set M).Definable LRV (mixedGammaGraph A.carrier ω))
    (hFinite : (gammaFormMap A ω hGraph).image.carrier.Finite)
    (hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ}) :
    ∃ T : MeasuredCoordinatePreparation (G := G) A C hCA (gammaFormMap A ω hGraph),
      ∀ i, (∀ a : Fin (n+1) → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ (C i).carrier}.Finite) →
      ∃ L : MeasuredRVLiftData (G := G) (C i) ((gammaFormMap A ω hGraph).comp (Map.inclusion (hCA i))),
        L.object.arity = T.arity ∧ ∀ p : C i, HEq (L.map p).val (T.map ⟨p.val,hCA i p.property⟩).val  := by
  apply lemma_6_21_finite_image_vfGenerated (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_33_finite_labels_vfGenerated` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_33_finite_labels_vfGenerated_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1) (hn : 0 < n)
    {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V)
    (hFin : U.object.domain.carrier.Finite) :
    ∃ H : MeasuredVFUnaryLiftChain (S : Set M) n U V, H.iso.iso.hom.map = e.iso.hom.map  := by
  apply lemma_6_33_finite_labels_vfGenerated (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_33_finite_labels_doublyBounded_vfGenerated` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_33_finite_labels_doublyBounded_vfGenerated_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1) (hn : 0 < n)
    {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V)
    (hFin : U.object.domain.carrier.Finite) (hU : U.doublyBounded) (hV : V.doublyBounded) :
    ∃ H : MeasuredVFUnaryLiftChain (S : Set M) n U V,
      H.iso.iso.hom.map = e.iso.hom.map ∧ H.properComponents ∧ ProperCovariantHomeomorphism H.lift.map  := by
  apply lemma_6_33_finite_labels_doublyBounded_vfGenerated (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_22` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_22_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : Set (Mixed M n r)) (hA : (rawMixedSpace (M := M) n r).Definable S A)
    (hVF : VFBounded A) (hRV : RVSupportDoublyBounded A) (f : Mixed M n r → Gamma M)
    (hf : S.Definable LRV (mixedGammaGraph A f)) (γ : Gamma M)
    (hconst : ∀ u, ∀ a ∈ vfFibre A u, ∀ b ∈ vfFibre A u,
      Congruent (fun _ => γ) a b → f (a,u) = f (b,u)) :
    ∃ δ : Gamma M, ∀ a ∈ A, δ⁻¹ ≤ f a ∧ f a ≤ δ  := by
  apply lemma_6_22 (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `corollary_6_23` with the unary Γ rational-affine input discharged. -/
theorem corollary_6_23_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : Set (Mixed M n r)} (hA : ProperInvariant S A) (f : Mixed M n r → Gamma M)
    (hf : S.Definable LRV (mixedGammaGraph A f))
    (hlevels : ∀ γ, ProperInvariantGeometry {p | p ∈ A ∧ f p = γ}) :
    ∃ δ : Gamma M, ∀ a ∈ A, δ⁻¹ ≤ f a ∧ f a ≤ δ  := by
  apply corollary_6_23 (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n r k : ℕ} {S : Set M}

/-- `lemma_6_21` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_21_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S) (hCA : ∀ i, (C i).carrier ⊆ A.carrier)
    (hC : ∀ i, ProperInvariant S (C i).carrier) (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier)
    (ω : Mixed M (n+1) r → Gamma M) (hGraph : S.Definable LRV (mixedGammaGraph A.carrier ω))
    (hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ}) :
    ∃ T : MeasuredCoordinatePreparation (G := G) A C hCA (gammaFormMap A ω hGraph),
      ∀ i, (∀ a : Fin (n+1) → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ (C i).carrier}.Finite) →
      ∃ L : MeasuredRVLiftData (G := G) (C i) ((gammaFormMap A ω hGraph).comp (Map.inclusion (hCA i))),
        L.object.arity = T.arity ∧ ∀ p : C i, HEq (L.map p).val (T.map ⟨p.val,hCA i p.property⟩).val  := by
  apply lemma_6_21 (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n r k : ℕ}

/-- `lemma_6_21_vfGenerated` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_21_vfGenerated_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) (S : Set M))
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) (S : Set M))
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant (S : Set M) (C i).carrier)
    (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier)
    (ω : Mixed M (n+1) r → Gamma M) (hGraph : (S : Set M).Definable LRV (mixedGammaGraph A.carrier ω))
    (hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ}) :
    ∃ T : MeasuredCoordinatePreparation (G := G) A C hCA (gammaFormMap A ω hGraph),
      ∀ i, (∀ a : Fin (n+1) → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ (C i).carrier}.Finite) →
      ∃ L : MeasuredRVLiftData (G := G) (C i) ((gammaFormMap A ω hGraph).comp (Map.inclusion (hCA i))),
        L.object.arity = T.arity ∧ ∀ p : C i, HEq (L.map p).val (T.map ⟨p.val,hCA i p.property⟩).val  := by
  apply lemma_6_21_vfGenerated (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n : ℕ}

/-- `lemma_6_33_doublyBounded_vfGenerated` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_33_doublyBounded_vfGenerated_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field,x ≠ 0 ∧ Valued.v x.val ≠ 1) (hn : 0 < n)
    {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V)
    (hU : U.doublyBounded) (hV : V.doublyBounded) :
    ∃ T : MeasuredVFUnaryLiftChain (S : Set M) n U V,T.iso.iso.hom.map=e.iso.hom.map ∧
      T.doublyBounded ∧ T.properComponents ∧ ProperCovariantHomeomorphism T.lift.map  := by
  apply lemma_6_33_doublyBounded_vfGenerated (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `proposition_6_19_vfGenerated` with the unary Γ rational-affine input discharged. -/
theorem proposition_6_19_vfGenerated_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) (S : Set M))
    (hA : ProperInvariant (S : Set M) A.carrier) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) (S : Set M))
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant (S : Set M) (P i).carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) n s) (S : Set M), ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant (S : Set M) B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (P i) (f.restrict (hPA i)).image (f.restrict (hPA i)).toImage ∧
        IsRVPullback (f.restrict (hPA i)).image.carrier  := by
  apply proposition_6_19_vfGenerated (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m k r s t : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}
variable {C : DefSet (rawMixedSpace (M := M) k t) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_9` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_9_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {f : Map A B} {g : Map B C}
    (hf : ProperCovariantHomeomorphism f) (hg : ProperCovariantHomeomorphism g) :
    ProperCovariantHomeomorphism (g.comp f)  := by
  apply lemma_6_9 (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_8` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_8_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hcov : ProperCovariant f) (hf : Function.Surjective f) :
    ProperInvariant S A.carrier ∧ ProperInvariant S B.carrier ∧
      (Function.Injective f → ContinuousOnGraphFibres f →
        ProperCovariantHomeomorphism f ∧
        ∀ (C : DefSet (rawMixedSpace (M := M) n r) S) (hCA : C.carrier ⊆ A.carrier),
          ProperInvariant S C.carrier → ProperCovariantHomeomorphism (f.restrict hCA).toImage)  := by
  apply lemma_6_8 (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_33_degree_one_vfGenerated` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_33_degree_one_vfGenerated_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {U V : MeasuredRVObject (M := M) (S : Set M) 1} (e : MeasuredRVIso U V)
    (hU : U.doublyBounded) (hV : V.doublyBounded) :
    ∃ f : Map (rvLift U.object) (rvLift V.object), ProperCovariantHomeomorphism f ∧
      VFUnaryRelativeAt f 0 ∧ (∀ p, e.iso.hom.map.graph p.val.2 (f p).val.2) ∧
      ∀ p, ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object (f p))).val  := by
  apply lemma_6_33_degree_one_vfGenerated (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `proposition_6_19` with the unary Γ rational-affine input discharged. -/
theorem proposition_6_19_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : ProperInvariant S A.carrier) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) n s) S, ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (P i) (f.restrict (hPA i)).image (f.restrict (hPA i)).toImage ∧
        IsRVPullback (f.restrict (hPA i)).image.carrier  := by
  apply proposition_6_19 (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_14_bounded_variable_apertures` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_14_bounded_variable_apertures_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} (h : RelativeApertureChain (G := G) A B f) :
    ProperCovariantHomeomorphism f ∧
      (n = 0 → ∀ p : A, HasMixedUnitDerivativeAt f p) ∧
      (0 < n → ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
        vfDim (rawRVSpace (M := M) 1) E < n ∧
        ∀ p : A, p.val ∉ E.carrier → HasMixedUnitDerivativeAt f p)  := by
  apply lemma_6_14_bounded_variable_apertures (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r q k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `remark_6_20` with the unary Γ rational-affine input discharged. -/
theorem remark_6_20_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V, iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ProperInvariant S A.carrier) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier)
    (Rel : DefSet (rawMixedSpace (M := M) (n+1) (r+q)) S) (hRel : ProperInvariant S Rel.carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) (n+1) s) S, ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      (∀ i, SpecialCovariantChain (G := G) (P i) (f.restrict (hPA i)).image (f.restrict (hPA i)).toImage ∧
        IsRVPullback (f.restrict (hPA i)).image.carrier) ∧
      ∀ p z : A, (f p).val.2 = (f z).val.2 → rvDataRow Rel p.val = rvDataRow Rel z.val  := by
  apply remark_6_20 (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_14` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_14_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} (h : SpecialCovariantChain (G := G) A B f) :
    ProperCovariantHomeomorphism f ∧
      (n = 0 → ∀ p : A, HasMixedUnitDerivativeAt f p) ∧
      (0 < n → ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
        vfDim (rawRVSpace (M := M) 1) E < n ∧
        ∀ p : A, p.val ∉ E.carrier → HasMixedUnitDerivativeAt f p)  := by
  apply lemma_6_14 (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_27` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_27_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
    (e : Equiv.Perm (Fin n)) : Nonempty (StandardContraction (G := G) A e)  := by
  apply lemma_6_27 (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_19_unary_vfGenerated` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_19_unary_vfGenerated_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (hA : ProperInvariant (S : Set M) A.carrier) (hARV : IsRVPullback A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant (S : Set M) (C i).carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) (S : Set M), ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant (S : Set M) B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
        IsRVPullback (f.restrict (hCA i)).image.carrier  := by
  apply lemma_6_19_unary_vfGenerated (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ} {S : Set M}

/-- `lemma_6_21_unary` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_21_unary_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) (hCA : ∀ i, (C i).carrier ⊆ A.carrier)
    (hC : ∀ i, ProperInvariant S (C i).carrier) (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier)
    (ω : Mixed M 1 r → Gamma M) (hGraph : S.Definable LRV (mixedGammaGraph A.carrier ω))
    (hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ}) :
    ∃ T : UnaryMeasuredPreparation (G := G) A C hCA (gammaFormMap A ω hGraph),
      ∀ i, (∀ a : Fin 1 → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ (C i).carrier}.Finite) →
      ∃ L : MeasuredRVLiftData (G := G) (C i) ((gammaFormMap A ω hGraph).comp (Map.inclusion (hCA i))),
        L.object.arity = T.arity ∧ ∀ p : C i, HEq (L.map p).val (T.map ⟨p.val,hCA i p.property⟩).val  := by
  apply lemma_6_21_unary (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ}

/-- `lemma_6_21_unary_vfGenerated` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_21_unary_vfGenerated_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant (S : Set M) (C i).carrier)
    (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier)
    (ω : Mixed M 1 r → Gamma M) (hGraph : (S : Set M).Definable LRV (mixedGammaGraph A.carrier ω))
    (hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ}) :
    ∃ T : UnaryMeasuredPreparation (G := G) A C hCA (gammaFormMap A ω hGraph),
      ∀ i, (∀ a : Fin 1 → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ (C i).carrier}.Finite) →
      ∃ L : MeasuredRVLiftData (G := G) (C i) ((gammaFormMap A ω hGraph).comp (Map.inclusion (hCA i))),
        L.object.arity = T.arity ∧ ∀ p : C i, HEq (L.map p).val (T.map ⟨p.val,hCA i p.property⟩).val  := by
  apply lemma_6_21_unary_vfGenerated (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_19_unary` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_19_unary_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hARV : IsRVPullback A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
        IsRVPullback (f.restrict (hCA i)).image.carrier  := by
  apply lemma_6_19_unary (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r q k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `remark_6_20_unary` with the unary Γ rational-affine input discharged. -/
theorem remark_6_20_unary_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i,(C i).carrier ⊆ A.carrier) (hC : ∀ i,ProperInvariant S (C i).carrier)
    (θ : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {x : Fin 1 → VF M | (x,u) ∈ A.carrier ∧ gammaFormExtension θ (x,u)=γ})
    (Rel : DefSet (rawMixedSpace (M := M) 1 (r+q)) S) (hRel : ProperInvariant S Rel.carrier) :
    ∃ s : ℕ,∃ B : DefSet (rawMixedSpace (M := M) 1 s) S,∃ f : Map A B,
      SynchronizedCentripetalChain (G := G) (Fin k) A B f C ∧
      ProperInvariant S B.carrier ∧ VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      (∀ p ∈ B.carrier,∀ z ∈ B.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1) ∧
      (∀ i,SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
        IsRVPullback (f.restrict (hCA i)).image.carrier) ∧
      (∃ U : UnaryContextLift (G := G) (unarySelfPreparationContext A hA hAD hARV hTag) f
          (Fin.elim0 : Fin 0 → DefSet (rawMixedSpace (M := M) 1 r) S),
        FormCompatibleSynchronizedChain (G := G) (Fin 0) A U.target.source U.map Fin.elim0 θ) ∧
      ∀ p z : A,(f p).val.2=(f z).val.2 → unaryRVDataRow Rel p.val=unaryRVDataRow Rel z.val  := by
  apply remark_6_20_unary (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- `lemma_6_27_unary` with the unary Γ rational-affine input discharged. -/
theorem lemma_6_27_unary_discharged
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (hA : ProperInvariant S A.carrier) :
    Nonempty (UnaryStandardContraction (G := G) A)  := by
  apply lemma_6_27_unary (linear := (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))) <;> assumption

end DiamondIntegral.Section6
end

end DischargedAll
