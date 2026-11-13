import «section 3».GammaGroundRVFamilyDesc
import «section 3».GammaGroundRVFamilyObjects
import «section 3».GammaGroundRVPackPairs
import «section 3».GammaGroundFiniteProducts
/-! Finite tags commute with actual cartesian RV products. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def GammaGroundFiniteFamily.rvProduct (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) k))
    (B : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) l)) : GammaGroundFiniteFamily hc ground (rawRVSpace (k + l)) :=
  ⟨A.tags * B.tags, fun i => gammaGroundRVProductDomain
    (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)⟩

def gammaGroundRVFamilyProductBranch (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) k))
    (B : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) l)) (i : Fin (A.tags * B.tags)) :
    GammaGroundMap ((A.rvProduct B).piece i) (gammaGroundRVProductDomain A.rvRealization B.rvRealization) :=
  (gammaGroundRVPack A.rvRealization B.rvRealization).toImage.comp
    ((GammaGroundMap.prodMap
      ((gammaGroundRVFamilyTagMap (finProdFinEquiv.symm i).1 (A.piece (finProdFinEquiv.symm i).1)).corestrict (B' := A.rvRealization)
        (fun a => ⟨_, a, rfl⟩))
      ((gammaGroundRVFamilyTagMap (finProdFinEquiv.symm i).2 (B.piece (finProdFinEquiv.symm i).2)).corestrict (B' := B.rvRealization)
        (fun b => ⟨_, b, rfl⟩))).comp
      (gammaGroundRVUnpack (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)))

def gammaGroundRVFamilyProductMap (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) k))
    (B : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) l)) :
    GammaGroundMap (A.rvProduct B).rvRealization (gammaGroundRVProductDomain A.rvRealization B.rvRealization) :=
  gammaGroundRVFamilyDesc (A.rvProduct B) _ (gammaGroundRVFamilyProductBranch A B)

theorem gammaGroundRVFamilyProductBranch_pair (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) k))
    (B : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) l)) (i : Fin (A.tags * B.tags))
    (a : A.piece (finProdFinEquiv.symm i).1) (b : B.piece (finProdFinEquiv.symm i).2) :
    gammaGroundRVFamilyProductBranch A B i (gammaGroundRVPackPair _ _ a b) =
      gammaGroundRVPackPair A.rvRealization B.rvRealization
        (A.rvEncode ⟨(finProdFinEquiv.symm i).1, a⟩)
        (B.rvEncode ⟨(finProdFinEquiv.symm i).2, b⟩) := by
  simp only [gammaGroundRVFamilyProductBranch, GammaGroundMap.comp_apply, gammaGroundRVUnpack_pair, GammaGroundMap.prodMap]
  rfl

theorem gammaGroundRVFamilyProductMap_bijective (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) k))
    (B : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) l)) : Function.Bijective (gammaGroundRVFamilyProductMap A B) := by
  constructor
  · intro x y he
    obtain ⟨⟨i, p⟩, rfl⟩ := (A.rvProduct B).rvEncode_bijective.surjective x
    obtain ⟨⟨j, q⟩, rfl⟩ := (A.rvProduct B).rvEncode_bijective.surjective y
    change gammaGroundRVFamilyDesc (A.rvProduct B) _ _ _ = gammaGroundRVFamilyDesc (A.rvProduct B) _ _ _ at he
    rw [gammaGroundRVFamilyDesc_encode, gammaGroundRVFamilyDesc_encode] at he
    obtain ⟨a, b, rfl⟩ := exists_gammaGroundRVPackPair (A.piece (finProdFinEquiv.symm i).1)
      (B.piece (finProdFinEquiv.symm i).2) p
    obtain ⟨c, d, rfl⟩ := exists_gammaGroundRVPackPair (A.piece (finProdFinEquiv.symm j).1)
      (B.piece (finProdFinEquiv.symm j).2) q
    rw [gammaGroundRVFamilyProductBranch_pair, gammaGroundRVFamilyProductBranch_pair] at he
    have hp := congrArg (gammaGroundRVUnpack A.rvRealization B.rvRealization) he
    simp only [gammaGroundRVUnpack_pair] at hp
    have ha := A.rvEncode_bijective.injective
      (Subtype.ext (congrArg (fun p : A.rvRealization.prod B.rvRealization => p.val.1) hp))
    have hb := B.rvEncode_bijective.injective
      (Subtype.ext (congrArg (fun p : A.rvRealization.prod B.rvRealization => p.val.2) hp))
    have hij : i = j := finProdFinEquiv.symm.injective
      (Prod.ext (congrArg Sigma.fst ha) (congrArg Sigma.fst hb))
    subst j
    have hac : a = c := by exact eq_of_heq (Sigma.mk.inj_iff.mp ha).2
    have hbd : b = d := by exact eq_of_heq (Sigma.mk.inj_iff.mp hb).2
    subst c
    subst d
    rfl
  · intro z
    obtain ⟨a, b, rfl⟩ := exists_gammaGroundRVPackPair A.rvRealization B.rvRealization z
    obtain ⟨⟨i, a⟩, rfl⟩ := A.rvEncode_bijective.surjective a
    obtain ⟨⟨j, b⟩, rfl⟩ := B.rvEncode_bijective.surjective b
    obtain ⟨q, hq⟩ := (finProdFinEquiv.symm : Fin (A.tags * B.tags) ≃ Fin A.tags × Fin B.tags).surjective (i, j)
    have hq1 := congrArg Prod.fst hq
    have hq2 := congrArg Prod.snd hq
    dsimp only [Prod.fst, Prod.snd] at hq1 hq2
    subst i
    subst j
    refine ⟨(A.rvProduct B).rvEncode ⟨q, gammaGroundRVPackPair _ _ a b⟩, ?_⟩
    change gammaGroundRVFamilyDesc (A.rvProduct B) _ _ _ = _
    rw [gammaGroundRVFamilyDesc_encode, gammaGroundRVFamilyProductBranch_pair]

def gammaGroundRVFamilyProductBijection (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) k))
    (B : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) l)) :
    GammaGroundBijection (A.rvProduct B).rvRealization (gammaGroundRVProductDomain A.rvRealization B.rvRealization) :=
  ⟨gammaGroundRVFamilyProductMap A B, gammaGroundRVFamilyProductMap_bijective A B⟩

end DiamondIntegral.Section3
