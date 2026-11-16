import «section 6».MeasuredCoordinateContraction

/-! Arithmetic on actual Gamma-valued definable maps. The complete
proper-code graphs live in the original structure and parameter base;
no RV representative is selected or adjoined as a parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def rawGammaBinaryMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : Gamma M → Gamma M → Gamma M)
    (hF : GammaSyntax.Definable S (fun z : ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) → Gamma M =>
      F (z (.inl (.inl 0))) (z (.inl (.inr 0))) = z (.inr 0))) :
    Map ((DefSet.univ (rawGammaPresentation (M := M)) S).prod
      (DefSet.univ (rawGammaPresentation (M := M)) S)) (DefSet.univ (rawGammaPresentation (M := M)) S) := by
  let A := (DefSet.univ (rawGammaPresentation (M := M)) S).prod (DefSet.univ (rawGammaPresentation (M := M)) S)
  let f (p : A) : DefSet.univ (rawGammaPresentation (M := M)) S := ⟨F p.val.1 p.val.2,Set.mem_univ _⟩
  refine ⟨f,?_⟩
  have h := hF
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) _
    {z : ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) → M | GammaSyntax.Proper z ∧ F (GammaParameters.codeValue (z (.inl (.inl 0))))
      (GammaParameters.codeValue (z (.inl (.inr 0)))) = GammaParameters.codeValue (z (.inr 0))} at h
  rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc] at h
  change S.Definable LRV ((rawGammaPresentation.prod rawGammaPresentation).relation rawGammaPresentation
    (fun x y => ∃ p : A, p.val = x ∧ (f p).val = y))
  convert h using 1 <;> try rfl
  apply Set.ext
  intro (z : ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) → M)
  constructor
  · rintro ⟨hxy,hout,p,hp,he⟩
    refine ⟨?_,?_⟩
    · rintro ((i | i) | i)
      · fin_cases i; exact hxy.1
      · fin_cases i; exact hxy.2
      · fin_cases i; exact hout
    · have hp' : p.val = (GammaParameters.codeValue (z (.inl (.inl 0))),
          GammaParameters.codeValue (z (.inl (.inr 0)))) := hp
      change F p.val.1 p.val.2 = GammaParameters.codeValue (z (.inr 0)) at he
      simpa only [hp'] using he
  · rintro ⟨hP,hRel⟩
    exact ⟨⟨hP (.inl (.inl 0)),hP (.inl (.inr 0))⟩,hP (.inr 0),
      ⟨(GammaParameters.codeValue (z (.inl (.inl 0))),GammaParameters.codeValue (z (.inl (.inr 0)))),
        Set.mem_univ _,Set.mem_univ _⟩,rfl,hRel⟩

def gammaMulMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  rawGammaBinaryMap (S := S) hc (fun a b : Gamma M => a*b)
    (GammaSyntax.mul_definable (M := M) (ι := ((Fin 1 ⊕ Fin 1) ⊕ Fin 1)) S (.inl (.inl 0)) (.inl (.inr 0)) (.inr 0))

def gammaDivMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  rawGammaBinaryMap (S := S) hc (fun a b : Gamma M => a/b)
    ((GammaSyntax.mul_definable (M := M) (ι := ((Fin 1 ⊕ Fin 1) ⊕ Fin 1)) S (.inr 0) (.inl (.inr 0)) (.inl (.inl 0))).congr
      (fun z => by
        constructor
        · intro h
          exact (div_eq_iff_eq_mul).mpr h.symm
        · intro h
          exact ((div_eq_iff_eq_mul).mp h).symm))

variable {P : SpecialTransformations.DefinableGeometry.Space LRV M} {A : DefSet P S}

def gammaMapMul (hc : CanonicalStructure.IsCanonical (M := M))
    (ω σ : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :=
  (gammaMulMap hc S).comp (ω.pair σ)

def gammaMapDiv (hc : CanonicalStructure.IsCanonical (M := M))
    (ω σ : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :=
  (gammaDivMap hc S).comp (ω.pair σ)

theorem gammaMapMul_at (hc : CanonicalStructure.IsCanonical (M := M))
    (ω σ : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (p : A) :
    (gammaMapMul hc ω σ p).val = gammaMapValue ω p * gammaMapValue σ p := rfl

theorem gammaMapDiv_at (hc : CanonicalStructure.IsCanonical (M := M))
    (ω σ : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (p : A) :
    (gammaMapDiv hc ω σ p).val = gammaMapValue ω p / gammaMapValue σ p := rfl

end DiamondIntegral.Section6
