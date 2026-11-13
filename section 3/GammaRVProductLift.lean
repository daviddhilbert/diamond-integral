import «section 3».GammaRVProductCodes
import «section 3».GammaRVLift
import «section 3».CarrierBijections
import «section 3».RVGradedSemiring

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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

def gammaRVProductFamilies (A : GammaObject hc S k) (B : GammaObject hc S l) :
    FamilyBijection (A.product B).rvPieces (A.rvPieces.rvProduct B.rvPieces) :=
  FamilyBijection.pieces (A.product B).rvPieces _ (fun i =>
    DefinableBijection.ofCarrierEq (gammaRVCodeLift_product
      (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)))

def gammaRVProductBijection (A : GammaObject hc S k) (B : GammaObject hc S l) :
    DefinableBijection (A.product B).rvLift.domain (A.rvLift.product B.rvLift).domain :=
  (rvFamilyProductBijection A.rvPieces B.rvPieces).comp (gammaRVProductFamilies A B).rvRealization

theorem gammaRVClass_product (A : GammaObject hc S k) (B : GammaObject hc S l) :
    rvClass (A.product B).rvLift = rvClass (A.rvLift.product B.rvLift) :=
  rvClass_iso (asIso (show (A.product B).rvLift ⟶ A.rvLift.product B.rvLift from
    gammaRVProductBijection A B))

def gammaRVUnitBijection :
    DefinableBijection (GammaObject.unit hc S).rvLift.domain (RVObject.unit (M := M) S).domain := by
  let A := (GammaObject.unit hc S).rvPieces
  let F : Map A.rvRealization (RVObject.unit (M := M) S).domain := Map.toSubsingleton _ (rawRVSpace 0)
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
    let c : codePreimage ((GammaObject.unit hc S).piece (0 : Fin 1)) :=
      ⟨⟨Fin.elim0 ∘ Prod.fst, fun i : Fin 0 => i.elim0⟩, Set.mem_univ _⟩
    refine ⟨A.rvEncode ⟨(0 : Fin 1), (gammaRVCodeBijection _).map c⟩, ?_⟩
    exact Subtype.ext (funext (fun i : Fin 0 => i.elim0))

theorem gammaRVClass_unit : rvClass (GammaObject.unit hc S).rvLift = rvClass (RVObject.unit (M := M) S) :=
  rvClass_iso (asIso (show (GammaObject.unit hc S).rvLift ⟶ RVObject.unit S from gammaRVUnitBijection))

end DiamondIntegral.Section3
