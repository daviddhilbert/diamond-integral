import «section 5».ElementaryRVValues
import «section 5».EmptyGammaSortedDefinability

/-! An actual native RV domain over the image of fixed real parameters
restricts canonically to the smaller model over those same parameters.
Actual RES finite support survives; all RV zeros are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
open Section3RVCodeBridge
variable {M N P : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
variable (hcM : CanonicalStructure.IsCanonical (M := M)) (hcN : CanonicalStructure.IsCanonical (M := N))
variable (e : M ↪ₑ[LRV] N) (c : P → M) {n : ℕ}

theorem elementaryRVSort_iff (x : M) : iRV (e x) ↔ iRV x := by
  have h := e.map_rel Rel.memRV ![x]
  have ht : (e ∘ (![x] : Fin 1 → M)) = ![e x] := by funext i;fin_cases i;rfl
  rw [ht] at h
  exact h

def elementaryNativeRawRestriction
    (D : GammaGroundDefSet hcN (EmptyGammaGround.base (Set.range (e ∘ c))) (rawRVSpace (M := N) n)) :
    LRV.DefinableSet (Set.range c) (Fin n) :=
  elementaryActualDefinableEquiv e c ⟨rawDomain D,emptyGamma_rawDomain_definable hcN _ D⟩

theorem elementaryNativeRawRestriction_sorted
    (D : GammaGroundDefSet hcN (EmptyGammaGround.base (Set.range (e ∘ c))) (rawRVSpace (M := N) n)) :
    ∀ x ∈ (elementaryNativeRawRestriction hcN e c D).val,∀ i,sortEval .rv (x i) := by
  intro x hx i
  have hm : e ∘ x ∈ rawDomain D := hx
  have hs := (rawDomain_definable D).proper (e ∘ x) hm i
  exact (elementaryRVSort_iff e (x i)).mp hs

def elementaryNativeRVRestriction
    (D : GammaGroundDefSet hcN (EmptyGammaGround.base (Set.range (e ∘ c))) (rawRVSpace (M := N) n)) :
    GammaGroundDefSet hcM (EmptyGammaGround.base (Set.range c)) (rawRVSpace (M := M) n) :=
  ofRaw (elementaryNativeRawRestriction hcN e c D).val
    ((emptyGamma_sorted_definable_iff hcM _ _ _).mpr
      ⟨(elementaryNativeRawRestriction hcN e c D).property,
        elementaryNativeRawRestriction_sorted hcN e c D⟩)

theorem elementaryNativeRVRestriction_mem
    (D : GammaGroundDefSet hcN (EmptyGammaGround.base (Set.range (e ∘ c))) (rawRVSpace (M := N) n))
    (x : Fin n → CanonicalRV.RVSort M) :
    x ∈ (elementaryNativeRVRestriction hcM hcN e c D).carrier ↔ elementaryRVMap e ∘ x ∈ D.carrier := by
  change e ∘ rvValues x ∈ rawDomain D ↔ _
  constructor
  · rintro ⟨u,hu,he⟩
    have hh : u = elementaryRVMap e ∘ x := rvValues_injective he
    exact hh ▸ hu
  · intro hx
    exact ⟨elementaryRVMap e ∘ x,hx,rfl⟩

theorem elementaryNativeRVRestriction_finite
    (D : GammaGroundDefSet hcN (EmptyGammaGround.base (Set.range (e ∘ c))) (rawRVSpace (M := N) n))
    (hD : GammaRVFiniteValues hcN _ D) :
    GammaRVFiniteValues hcM _ (elementaryNativeRVRestriction hcM hcN e c D) := by
  apply (elementaryRV_finite_values_restrict e D.carrier hD).subset
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨x,(elementaryNativeRVRestriction_mem hcM hcN e c D x).mp hx,rfl⟩

def elementaryNativeRESRestriction {k : ℕ}
    (U : GammaGroundRESObject hcN (EmptyGammaGround.base (Set.range (e ∘ c))) k) :
    GammaGroundRESObject hcM (EmptyGammaGround.base (Set.range c)) U.obj.arity :=
  nativeRESObjectOfGammaSet hcM _ (elementaryNativeRVRestriction hcM hcN e c U.obj.domain)
    (elementaryNativeRVRestriction_finite hcM hcN e c U.obj.domain U.property)

end DiamondIntegral.Section5
