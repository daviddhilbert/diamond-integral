import «section 6».RawParameterRelations
import «section 6».GraphFibres

/-! Universal conditions on actual mixed tuples are first-order
parameter loci. The sorted raw domain is retained, so untyped real
tuples impose no extra admissibility requirements. -/

noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {ι : Type} [Finite ι] {n r : ℕ}

def mixedAllParameterLocus (n r : ℕ) (R : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) : Set (ι → M) :=
  rawRowSubsetParameterLocus {z | z ∘ Sum.inr ∈ (rawMixedSpace (M := M) n r).domain} R

theorem mixedAllParameterLocus_definable
    (R : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (mixedAllParameterLocus n r R) :=
  rawRowSubsetParameterLocus_definable _ _ ((rawMixedSpace (M := M) n r).definable_domain S |>.preimage_comp Sum.inr) hR

theorem mixedAllParameterLocus_at (R : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) (a : ι → M) :
    a ∈ mixedAllParameterLocus n r R ↔ ∀ q : Mixed M n r,Sum.elim a (mixedValues q) ∈ R := by
  change (∀ z : Fin n ⊕ Fin r → M,z ∉ (rawMixedSpace (M := M) n r).domain ∨ Sum.elim a z ∈ R) ↔ _
  constructor
  · intro h q
    exact (h (mixedValues q)).resolve_left (not_not.mpr (mixedValues_mem_domain q))
  · intro h z
    by_cases hz : z ∈ (rawMixedSpace (M := M) n r).domain
    · right
      let q := (rawMixedSpace (M := M) n r).decode ⟨z,hz⟩
      have he : mixedValues q=z := mixedValues_decode ⟨z,hz⟩
      have hq := h q
      rwa [he] at hq
    · exact Or.inl hz

end DiamondIntegral.Section6
