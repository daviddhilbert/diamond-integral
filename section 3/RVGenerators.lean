import «section 3».RVGradedComparison
import «section 3».GroupifiedCongruences
import «section 3».MeasuredRVProducts
import Section3.GammaRVSeparation

/-! The elementary relation uses the actual degree-one point and the
strictly positive value domain. Infinity contributes the degree-zero unit. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def rvOneDomain (S : Set M) : DefSet (rawRVSpace (M := M) 1) S :=
  (rvRightTagMap (RVObject.unit S).domain 0).image

def rvOneObject (S : Set M) : RVObject (M := M) S 1 where
  arity := 1
  domain := rvOneDomain S
  volume := Map.inclusion (fun _ _ => Set.mem_univ _)
  finite := Map.finiteFibres_of_injective (by
    intro a b he
    exact Subtype.ext (congrArg (fun c : DefSet.univ (rawRVSpace 1) S => c.val) he))
  nonzero a i := by
    obtain ⟨u, hu⟩ := a.property
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (a.val 0).val ≠ iRVZero
    rw [← hu]
    change iRVOne ≠ iRVZero
    exact RVCalc.rv_one_ne_zero (inferInstance : M ⊨ Axioms.ACVF)

def rvPositiveDomain (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    DefSet (rawRVSpace (M := M) 1) S where
  carrier := {t | (t 0).val ≠ iRVZero ∧ GammaParameters.EndpointLogic.codeLt iRVOne (t 0).val}
  definable := by
    have hl := GammaParameters.EndpointLogic.codeLt_definable (M := M) S
    rw [normalize_eq_of_isCanonical hc] at hl
    have hF : S.DefinableMap LRV (fun z : Fin 1 → M => (![iRVOne, z 0] : Fin 2 → M)) := by
      intro i
      fin_cases i
      · change S.DefinableFun LRV (fun _ : Fin 1 → M => iRVOne)
        simpa using
          rvConstantCode_definable (M := M) S (ι := Fin 1) true
      · change S.DefinableFun LRV (fun z : Fin 1 → M => z 0)
        exact
          (Set.DefinableFun.proj (M := M) LRV (A := S) (i := (0 : Fin 1)))
    have hlt := hl.preimage_map hF
    have hz := rvConstantCode_definable (M := M) S (ι := Fin 1) false
    have hn := ((Set.DefinableFun.proj LRV (A := S) (i := (0 : Fin 1))).ofPred_eq hz).compl
    have hlt' : S.Definable LRV {z : Fin 1 → M | GammaParameters.EndpointLogic.codeLt iRVOne (z 0)} := by
      simpa using hlt
    have hn' : S.Definable LRV {z : Fin 1 → M | z 0 ≠ iRVZero} := by
      simpa only [Bool.false_eq_true, ↓reduceIte, Set.compl_setOf] using hn
    have hd := ((rawRVSpace (M := M) 1).definable_domain S).inter (hn'.inter hlt')
    change S.Definable LRV _
    convert hd using 1
    ext z
    constructor
    · rintro ⟨hz, hn, hl⟩
      refine ⟨hz, ?_, ?_⟩
      · change rvValues ((rawRVSpace 1).decode ⟨z, hz⟩) 0 ≠ iRVZero at hn
        simpa only [rvValues_decode, Set.mem_ofPred_eq] using hn
      · change GammaParameters.EndpointLogic.codeLt iRVOne
          (rvValues ((rawRVSpace 1).decode ⟨z, hz⟩) 0) at hl
        simpa only [rvValues_decode, Set.mem_ofPred_eq] using hl
    · rintro ⟨hz, hn, hl⟩
      refine ⟨hz, ?_, ?_⟩
      · change rvValues ((rawRVSpace 1).decode ⟨z, hz⟩) 0 ≠ iRVZero
        simpa only [rvValues_decode, Set.mem_ofPred_eq] using hn
      · change GammaParameters.EndpointLogic.codeLt iRVOne
          (rvValues ((rawRVSpace 1).decode ⟨z, hz⟩) 0)
        simpa only [rvValues_decode, Set.mem_ofPred_eq] using hl

def rvPositiveObject (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    RVObject (M := M) S 1 where
  arity := 1
  domain := rvPositiveDomain hc S
  volume := Map.inclusion (fun _ _ => Set.mem_univ _)
  finite := Map.finiteFibres_of_injective (by
    intro a b he
    exact Subtype.ext (congrArg (fun c : DefSet.univ (rawRVSpace 1) S => c.val) he))
  nonzero a i := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact a.property.1

def rvSpecialCongruence (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    RingCon (RVPositiveSemiring (M := M) S) :=
  ringConGen (fun x y => x = rvSemiringClass (rvOneObject S) ∧
    y = rvSemiringClass (rvPositiveObject hc S) + 1)

def rvPrincipalElement (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    RVGrothendieckRing (M := M) S :=
  Algebra.GrothendieckAddGroup.of (rvSemiringClass (rvOneObject S)) -
    Algebra.GrothendieckAddGroup.of (rvSemiringClass (rvPositiveObject hc S))

def rvSpecialCompletionEquiv (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    RingCompletion (rvSpecialCongruence hc S).Quotient ≃+*
      RVGrothendieckRing S ⧸ Ideal.span ({rvPrincipalElement hc S - 1} : Set (RVGrothendieckRing S)) :=
  groupifiedUnmeasuredRelation (rvSemiringClass (rvOneObject S)) (rvSemiringClass (rvPositiveObject hc S))

end DiamondIntegral.Section3
