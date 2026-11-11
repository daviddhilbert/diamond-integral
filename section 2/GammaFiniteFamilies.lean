import «section 2».Conventions
import Section3.GammaRVSeparation
import Section3.FiniteImage
import Section4.RealPresentations

/-!
# Finite VF families indexed by actual Gamma values

Every nonzero RV code of each Gamma value is retained in the full graph.
The checked finite-valued RV-to-VF theorem gives finiteness of the union,
over the original real parameter base, in every finite VF output arity.
This is the radius-selection step in the proposed fibrewise openness proof.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def gammaIndexedFamilyGraph (F : Gamma M → Set (Fin n → VF M)) :
    Set (Fin 1 ⊕ Fin n → M) :=
  {z | GammaParameters.NonzeroRV (z (.inl 0)) ∧
    ∃ y ∈ F (GammaParameters.codeValue (z (.inl 0))), vfValues y = z ∘ Sum.inr}

theorem gamma_indexed_finite_union
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (F : Gamma M → Set (Fin n → VF M))
    (hG : S.Definable LRV (gammaIndexedFamilyGraph F))
    (hfin : ∀ γ, (F γ).Finite) : (⋃ γ, F γ).Finite := by
  have hsort (t : Fin 1 → M) (y : Fin n → M)
      (hy : Sum.elim t y ∈ gammaIndexedFamilyGraph F) :
      (∀ j, iRV (t j)) ∧ ∀ j, iVF (y j) := by
    obtain ⟨ht, b, _, hb⟩ := hy
    constructor
    · intro j
      fin_cases j
      exact ht.1
    · intro j
      have he : (b j).val = y j := congrFun hb j
      exact he ▸ (b j).property
  have hfraw (t : Fin 1 → M) :
      {y : Fin n → M | Sum.elim t y ∈ gammaIndexedFamilyGraph F}.Finite := by
    apply ((hfin (GammaParameters.codeValue (t 0))).image vfValues).subset
    rintro y ⟨_, b, hb, he⟩
    exact ⟨b, hb, he⟩
  have hraw := finite_rv_to_vf_tuple_relation_image hc hs S hsmall
    (gammaIndexedFamilyGraph F) hG hsort hfraw
  apply (hraw.preimage vfValues_injective.injOn).subset
  intro y hy
  obtain ⟨γ, hy⟩ := Set.mem_iUnion.mp hy
  obtain ⟨u, hu, he⟩ := GammaParameters.EndpointLogic.codeValue_surjective γ
  refine ⟨![u], ?_⟩
  change GammaParameters.NonzeroRV u ∧
    ∃ b ∈ F (GammaParameters.codeValue u), vfValues b = vfValues y
  exact ⟨hu, y, he.symm ▸ hy, rfl⟩

/-- An infinite definable union has an infinite fibre; no ordering or
definable section of the value-group quotient is needed. -/
theorem exists_infinite_gamma_fibre
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (F : Gamma M → Set (Fin n → VF M))
    (hG : S.Definable LRV (gammaIndexedFamilyGraph F))
    (hUnion : (⋃ γ, F γ).Infinite) : ∃ γ, (F γ).Infinite := by
  classical
  by_contra hn
  apply hUnion
  apply gamma_indexed_finite_union hc hs hsmall F hG
  intro γ
  by_contra hi
  exact hn ⟨γ, hi⟩

end DiamondIntegral.Section2
