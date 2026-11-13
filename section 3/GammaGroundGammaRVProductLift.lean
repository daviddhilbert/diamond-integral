import «section 3».GammaGroundGammaRVProductCodes
import «section 3».GammaGroundGammaRVLift
import «section 3».GammaGroundCarrierBijections
import «section 3».GammaGroundRVGradedSemiring
import «section 3».GammaGroundRVFamilyProducts
/-! The full Gamma lift respects actual cartesian multiplication and
the degree-zero unit. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def gammaGroundGammaRVProductFamilies (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l) :
    GammaGroundFamilyBijection (A.product B).rvPieces (A.rvPieces.rvProduct B.rvPieces) :=
  GammaGroundFamilyBijection.pieces (A.product B).rvPieces _ (fun i =>
    GammaGroundBijection.ofCarrierEq (gammaGroundGammaRVCodeLift_product
      (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)))

def gammaGroundGammaRVProductBijection (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l) :
    GammaGroundBijection (A.product B).rvLift.domain (A.rvLift.product B.rvLift).domain :=
  (gammaGroundRVFamilyProductBijection A.rvPieces B.rvPieces).comp (gammaGroundGammaRVProductFamilies A B).rvRealization

theorem gammaGroundGammaRVClass_product (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l) :
    gammaGroundRVClass (A.product B).rvLift = gammaGroundRVClass (A.rvLift.product B.rvLift) :=
  gammaGroundRVClass_iso (asIso (show (A.product B).rvLift ⟶ A.rvLift.product B.rvLift from
    gammaGroundGammaRVProductBijection A B))

def gammaGroundGammaRVUnitBijection :
    GammaGroundBijection (GammaGroundGammaObject.unit hc ground).rvLift.domain (GammaGroundRVObject.unit (M := M) hc ground).domain := by
  let A := (GammaGroundGammaObject.unit hc ground).rvPieces
  let F : GammaGroundMap A.rvRealization (GammaGroundRVObject.unit (M := M) hc ground).domain := GammaGroundMap.ofGlobal _ _ (Map.toSubsingleton (DefSet.univ (rawRVSpace (1 + 0)) ground.real) (rawRVSpace 0)) (fun _ => Set.mem_univ _)
  refine ⟨F, ?_, ?_⟩
  · intro x y _
    obtain ⟨⟨i, a⟩, rfl⟩ := A.rvEncode_bijective.surjective x
    obtain ⟨⟨j, b⟩, rfl⟩ := A.rvEncode_bijective.surjective y
    have hij : i = j := Subsingleton.elim (show Fin 1 from i) (show Fin 1 from j)
    subst j
    have hab : a = b := Subtype.ext (funext (fun i : Fin 0 => i.elim0))
    subst b
    rfl
  · intro b
    let c : gammaGroundCodePreimage ((GammaGroundGammaObject.unit hc ground).piece (0 : Fin 1)) :=
      ⟨⟨Fin.elim0 ∘ Prod.fst, fun i : Fin 0 => i.elim0⟩, Set.mem_univ _⟩
    refine ⟨A.rvEncode ⟨(0 : Fin 1), (gammaGroundGammaRVCodeBijection _).map c⟩, ?_⟩
    exact Subtype.ext (funext (fun i : Fin 0 => i.elim0))

theorem gammaGroundGammaRVClass_unit : gammaGroundRVClass (GammaGroundGammaObject.unit hc ground).rvLift = gammaGroundRVClass (GammaGroundRVObject.unit (M := M) hc ground) :=
  gammaGroundRVClass_iso (asIso (show (GammaGroundGammaObject.unit hc ground).rvLift ⟶ GammaGroundRVObject.unit hc ground from gammaGroundGammaRVUnitBijection))

end DiamondIntegral.Section3
