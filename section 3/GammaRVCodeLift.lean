import «section 3».GammaCategories
import «section 3».RESScissors
import Section4.RVCoordinates

/-! A Gamma piece lifts to the complete set of its nonzero RV codes,
with the literal identity target. No representative is selected in a
valuation fibre. Finite Gamma pieces have finite domain-value support. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

abbrev GammaPiece (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  DefSet ((volumeGammaSpace hc).power (Fin k)) S

def gammaCodeTuple (c : (codeSpace ((volumeGammaSpace hc).power (Fin k))).Carrier) :
    Fin k → CanonicalRV.RVSort M :=
  fun i => ⟨c.val (i, (0 : Fin 1)), (c.property i).1⟩

def gammaCodeToRV (I : GammaPiece hc S k) :
    Map (codePreimage I) (DefSet.univ (rawRVSpace k) S) := by
  let F (z : (Fin k × Fin 1) → M) : Fin k → M := fun i => z (i, 0)
  refine Map.ofCodes (codePreimage I) gammaCodeTuple F
    (fun _ => Set.DefinableFun.proj LRV) ?_ ?_
  · intro c
    exact ⟨gammaCodeTuple c, rfl⟩
  · intro c
    apply rvValues_injective
    exact rvValues_decode _

theorem gammaCodeToRV_injective (I : GammaPiece hc S k) :
    Function.Injective (gammaCodeToRV I) := by
  intro a b he
  apply Subtype.ext
  apply Subtype.ext
  funext ⟨i, j⟩
  change Fin 1 at j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  exact congrArg (fun t : DefSet.univ (rawRVSpace k) S => (t.val i).val) he

def gammaRVCodeLift (I : GammaPiece hc S k) : RVObject S k where
  arity := k
  domain := (gammaCodeToRV I).image
  volume := Map.inclusion (fun _ _ => Set.mem_univ _)
  finite := Map.finiteFibres_of_injective (by
    intro a b he
    exact Subtype.ext (congrArg (fun t : DefSet.univ (rawRVSpace k) S => t.val) he))
  nonzero a i := by
    obtain ⟨c, hc⟩ := a.property
    change (a.val i).val ≠ iRVZero
    rw [← hc]
    exact (c.val.property i).2

def gammaRVCodeBijection (I : GammaPiece hc S k) :
    DefinableBijection (codePreimage I) (gammaRVCodeLift I).domain :=
  ⟨(gammaCodeToRV I).toImage, by
    constructor
    · intro a b he
      apply gammaCodeToRV_injective I
      exact Subtype.ext (congrArg (fun c : (gammaCodeToRV I).image => c.val) he)
    · intro b
      obtain ⟨a, ha⟩ := b.property
      exact ⟨a, Subtype.ext ha⟩⟩

theorem gammaRVCodeLift_res (I : GammaPiece hc S k) (hI : I.carrier.Finite) :
    resProperty S k (gammaRVCodeLift I) := by
  let values (α : Fin k → Values.Gamma (M := M)) := fun i => (α i).val
  apply (hI.image values).subset
  rintro _ ⟨t, ⟨c, ht⟩, rfl⟩
  refine ⟨((volumeGammaSpace hc).power (Fin k)).decode c.val, c.property, ?_⟩
  rw [← ht]
  rfl

def gammaRESCodeLift (I : GammaPiece hc S k) (hI : I.carrier.Finite) : RESObject S k :=
  ⟨gammaRVCodeLift I, gammaRVCodeLift_res I hI⟩

def gammaRVCodeIso {I J : GammaPiece hc S k}
    (f : DefinableBijection (codePreimage I) (codePreimage J)) :
    gammaRVCodeLift I ≅ gammaRVCodeLift J :=
  CategoryTheory.asIso ((gammaRVCodeBijection J).comp
    (f.comp (gammaRVCodeBijection I).symm))

end DiamondIntegral.Section3
