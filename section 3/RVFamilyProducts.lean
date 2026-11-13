import «section 3».RVFamilyDesc
import «section 3».RVFamilyObjects
import Section4.RVProductAssociativity

/-! Finite tags commute with actual cartesian RV products. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

def FiniteFamily.rvProduct (A : FiniteFamily (rawRVSpace (M := M) k) S)
    (B : FiniteFamily (rawRVSpace (M := M) l) S) : FiniteFamily (rawRVSpace (k + l)) S :=
  ⟨A.tags * B.tags, fun i => rvProductDomain
    (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)⟩

def rvFamilyProductBranch (A : FiniteFamily (rawRVSpace (M := M) k) S)
    (B : FiniteFamily (rawRVSpace (M := M) l) S) (i : Fin (A.tags * B.tags)) :
    Map ((A.rvProduct B).piece i) (rvProductDomain A.rvRealization B.rvRealization) :=
  (rvPack A.rvRealization B.rvRealization).toImage.comp
    ((Map.prodMap
      ((rvFamilyTagMap (finProdFinEquiv.symm i).1 (A.piece (finProdFinEquiv.symm i).1)).corestrict (B' := A.rvRealization)
        (fun a => ⟨_, a, rfl⟩))
      ((rvFamilyTagMap (finProdFinEquiv.symm i).2 (B.piece (finProdFinEquiv.symm i).2)).corestrict (B' := B.rvRealization)
        (fun b => ⟨_, b, rfl⟩))).comp
      (rvUnpack (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)))

def rvFamilyProductMap (A : FiniteFamily (rawRVSpace (M := M) k) S)
    (B : FiniteFamily (rawRVSpace (M := M) l) S) :
    Map (A.rvProduct B).rvRealization (rvProductDomain A.rvRealization B.rvRealization) :=
  rvFamilyDesc (A.rvProduct B) _ (rvFamilyProductBranch A B)

theorem rvFamilyProductBranch_pair (A : FiniteFamily (rawRVSpace (M := M) k) S)
    (B : FiniteFamily (rawRVSpace (M := M) l) S) (i : Fin (A.tags * B.tags))
    (a : A.piece (finProdFinEquiv.symm i).1) (b : B.piece (finProdFinEquiv.symm i).2) :
    rvFamilyProductBranch A B i (rvPackPair _ _ a b) =
      rvPackPair A.rvRealization B.rvRealization
        (A.rvEncode ⟨(finProdFinEquiv.symm i).1, a⟩)
        (B.rvEncode ⟨(finProdFinEquiv.symm i).2, b⟩) := by
  simp only [rvFamilyProductBranch, Map.comp_apply, rvUnpack_pair, Map.prodMap_mk]
  rfl

theorem rvFamilyProductMap_bijective (A : FiniteFamily (rawRVSpace (M := M) k) S)
    (B : FiniteFamily (rawRVSpace (M := M) l) S) : Function.Bijective (rvFamilyProductMap A B) := by
  constructor
  · intro x y he
    obtain ⟨⟨i, p⟩, rfl⟩ := (A.rvProduct B).rvEncode_bijective.surjective x
    obtain ⟨⟨j, q⟩, rfl⟩ := (A.rvProduct B).rvEncode_bijective.surjective y
    change rvFamilyDesc (A.rvProduct B) _ _ _ = rvFamilyDesc (A.rvProduct B) _ _ _ at he
    rw [rvFamilyDesc_encode, rvFamilyDesc_encode] at he
    obtain ⟨a, b, rfl⟩ := exists_rvPackPair (A.piece (finProdFinEquiv.symm i).1)
      (B.piece (finProdFinEquiv.symm i).2) p
    obtain ⟨c, d, rfl⟩ := exists_rvPackPair (A.piece (finProdFinEquiv.symm j).1)
      (B.piece (finProdFinEquiv.symm j).2) q
    rw [rvFamilyProductBranch_pair, rvFamilyProductBranch_pair] at he
    have hp := congrArg (rvUnpack A.rvRealization B.rvRealization) he
    simp only [rvUnpack_pair] at hp
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
    obtain ⟨a, b, rfl⟩ := exists_rvPackPair A.rvRealization B.rvRealization z
    obtain ⟨⟨i, a⟩, rfl⟩ := A.rvEncode_bijective.surjective a
    obtain ⟨⟨j, b⟩, rfl⟩ := B.rvEncode_bijective.surjective b
    obtain ⟨q, hq⟩ := (finProdFinEquiv.symm : Fin (A.tags * B.tags) ≃ Fin A.tags × Fin B.tags).surjective (i, j)
    have hq1 := congrArg Prod.fst hq
    have hq2 := congrArg Prod.snd hq
    dsimp only [Prod.fst, Prod.snd] at hq1 hq2
    subst i
    subst j
    refine ⟨(A.rvProduct B).rvEncode ⟨q, rvPackPair _ _ a b⟩, ?_⟩
    change rvFamilyDesc (A.rvProduct B) _ _ _ = _
    rw [rvFamilyDesc_encode, rvFamilyProductBranch_pair]

def rvFamilyProductBijection (A : FiniteFamily (rawRVSpace (M := M) k) S)
    (B : FiniteFamily (rawRVSpace (M := M) l) S) :
    DefinableBijection (A.rvProduct B).rvRealization (rvProductDomain A.rvRealization B.rvRealization) :=
  ⟨rvFamilyProductMap A B, rvFamilyProductMap_bijective A B⟩

end DiamondIntegral.Section3
