import «section 2».UniformGammaSuprema
import Section4.GammaPredicates
import Section8.GammaRadiusBase

/-! A uniformly definable family indexed by actual Gamma values has a
definable supremum function when every indicated supremum exists. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def gammaDomainCodes (D : Set (Gamma M)) : Set (Fin 1 → M) :=
  {x | GammaParameters.NonzeroRV (x 0) ∧ GammaParameters.codeValue (x 0) ∈ D}

theorem gammaDomainCodes_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (D : Set (Gamma M)) (hD : GammaSyntax.Definable S (fun x : Fin 1 → Gamma M => x 0 ∈ D)) :
    S.Definable LRV (gammaDomainCodes D) := by
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 1)
    {x | GammaSyntax.Proper x ∧ GammaParameters.codeValue (x 0) ∈ D} at hD
  rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc] at hD
  convert hD using 1
  ext x
  exact and_congr (by constructor; intro h j; fin_cases j; exact h; intro h; exact h 0) Iff.rfl

theorem uniform_gamma_domain_supremum (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (D : Set (Gamma M)) (P : Gamma M → Set (Gamma M))
    (hD : S.Definable LRV (gammaDomainCodes D))
    (hP : S.Definable LRV (rawGammaFamilyGraph (gammaDomainCodes D)
      (fun x => P (GammaParameters.codeValue (x 0)))))
    (hexists : ∀ γ ∈ D, ∃ c : Gamma M, IsLUB (P γ) c) :
    ∃ f : Gamma M → Gamma M,
      GammaSyntax.Definable S (fun z : Fin 2 → Gamma M => z 0 ∈ D ∧ f (z 0) = z 1) ∧
        ∀ γ ∈ D, IsLUB (P γ) (f γ) := by
  classical
  let f (γ : Gamma M) : Gamma M := if hγ : γ ∈ D then (hexists γ hγ).choose else 1
  have hf : ∀ γ ∈ D, IsLUB (P γ) (f γ) := by
    intro γ hγ
    simpa only [f,dite_eq_left hγ] using (hexists γ hγ).choose_spec
  have hLUB := rawGammaLUBGraph_definable S (gammaDomainCodes D) hD
    (fun x => P (GammaParameters.codeValue (x 0))) hP
  let idx : Fin 1 ⊕ Fin 1 → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)
  have hraw := hLUB.preimage_comp idx
  refine ⟨f,?_,hf⟩
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
    {z | GammaSyntax.Proper z ∧ GammaParameters.codeValue (z 0) ∈ D ∧
      f (GammaParameters.codeValue (z 0)) = GammaParameters.codeValue (z 1)}
  rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc]
  convert hraw using 1
  ext z
  change ((∀ i : Fin 2, GammaParameters.NonzeroRV (z i)) ∧
    GammaParameters.codeValue (z 0) ∈ D ∧ f (GammaParameters.codeValue (z 0)) = GammaParameters.codeValue (z 1)) ↔
    ((GammaParameters.NonzeroRV (z 0) ∧ GammaParameters.codeValue (z 0) ∈ D) ∧
      GammaParameters.NonzeroRV (z 1) ∧ IsLUB (P (GammaParameters.codeValue (z 0))) (GammaParameters.codeValue (z 1)))
  constructor
  · rintro ⟨hz,hzD,he⟩
    exact ⟨⟨hz 0,hzD⟩,hz 1,he ▸ hf _ hzD⟩
  · rintro ⟨⟨h0,hzD⟩,h1,hL⟩
    refine ⟨?_,hzD,(hf _ hzD).unique hL⟩
    intro j
    fin_cases j
    · exact h0
    · exact h1

end DiamondIntegral.Section2
