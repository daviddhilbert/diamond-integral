import «section 3».GammaGroundGammaCategories
import «section 3».GammaGroundRESScissors
import «section 3».GammaRVCodeLift

/-! Each Gamma-ground piece lifts to all of its nonzero RV codes.
The actual identity target and finite domain-value support are retained. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

abbrev GammaGroundGammaPiece (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  GammaGroundDefSet hc ground ((volumeGammaSpace hc).power (Fin k))

def gammaGroundGammaCodeToRV (I : GammaGroundGammaPiece hc ground k) :
    GammaGroundMap (gammaGroundCodePreimage I) (GammaGroundDefSet.univ hc ground (rawRVSpace k)) :=
  GammaGroundMap.ofGlobal _ _ (gammaCodeToRV (DefSet.univ ((volumeGammaSpace hc).power (Fin k)) ground.real))
    (fun _ => Set.mem_univ _)

theorem gammaGroundGammaCodeToRV_injective (I : GammaGroundGammaPiece hc ground k) :
    Function.Injective (gammaGroundGammaCodeToRV I) := by
  intro a b he
  apply Subtype.ext
  apply Subtype.ext
  funext ⟨i, j⟩
  change Fin 1 at j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  exact congrArg (fun t : GammaGroundDefSet.univ hc ground (rawRVSpace k) => (t.val i).val) he

def gammaGroundGammaRVCodeLift (I : GammaGroundGammaPiece hc ground k) : GammaGroundRVObject hc ground k where
  arity := k
  domain := (gammaGroundGammaCodeToRV I).image
  volume := GammaGroundMap.inclusion (fun _ _ => Set.mem_univ _)
  finite := GammaGroundMap.finiteFibres_of_injective (by
    intro a b he
    exact Subtype.ext (congrArg (fun t : GammaGroundDefSet.univ hc ground (rawRVSpace k) => t.val) he))
  nonzero a i := by
    obtain ⟨c, he⟩ := a.property
    change (a.val i).val ≠ iRVZero
    rw [← he]
    exact (c.val.property i).2

def gammaGroundGammaRVCodeBijection (I : GammaGroundGammaPiece hc ground k) :
    GammaGroundBijection (gammaGroundCodePreimage I) (gammaGroundGammaRVCodeLift I).domain :=
  ⟨(gammaGroundGammaCodeToRV I).toImage,
    (gammaGroundGammaCodeToRV I).toImage_bijective (gammaGroundGammaCodeToRV_injective I)⟩

theorem gammaGroundGammaRVCodeLift_res (I : GammaGroundGammaPiece hc ground k) (hI : I.carrier.Finite) :
    gammaGroundResProperty (gammaGroundGammaRVCodeLift I) := by
  let values (α : Fin k → Values.Gamma (M := M)) := fun i => (α i).val
  apply (hI.image values).subset
  rintro _ ⟨t, ⟨c, ht⟩, rfl⟩
  refine ⟨((volumeGammaSpace hc).power (Fin k)).decode c.val, c.property, ?_⟩
  rw [← ht]
  rfl

def gammaGroundGammaRESCodeLift (I : GammaGroundGammaPiece hc ground k) (hI : I.carrier.Finite) :
    GammaGroundRESObject hc ground k := ⟨gammaGroundGammaRVCodeLift I, gammaGroundGammaRVCodeLift_res I hI⟩

def gammaGroundGammaRVCodeIso {I J : GammaGroundGammaPiece hc ground k}
    (f : GammaGroundBijection (gammaGroundCodePreimage I) (gammaGroundCodePreimage J)) :
    gammaGroundGammaRVCodeLift I ≅ gammaGroundGammaRVCodeLift J :=
  asIso (show _ ⟶ _ from (gammaGroundGammaRVCodeBijection J).comp (f.comp (gammaGroundGammaRVCodeBijection I).symm))

end DiamondIntegral.Section3
