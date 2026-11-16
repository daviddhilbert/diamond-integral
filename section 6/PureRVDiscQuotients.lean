import «section 6».FiniteRVFiberTransport

/-! Actual pure-RV disc quotients of tagged mixed domains, including
the definable map recording their VF leading terms. These use complete
original-base graphs and actual surjective descent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def vfLeadingTermMap (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Map A (DefSet.univ (rawRVSpace (M := M) n) S) := by
  let P := rawMixedSpace (M := M) n r
  let codes (z : Fin n ⊕ Fin r → M) : Fin n → M := fun i => iRv (z (.inl i))
  have hCodes : S.DefinableMap LRV codes := fun i => rv_scalarCode_definable (Set.DefinableFun.proj LRV)
  have hCode (c : P.domain) : rvValues (tupleRV M (P.decode c).1) = codes c.val := by
    funext i
    exact congrArg iRv (congrFun (mixedValues_decode c) (.inl i))
  have hDom (c : P.domain) : codes c.val ∈ (rawRVSpace (M := M) n).domain :=
    ⟨tupleRV M (P.decode c).1,hCode c⟩
  refine Map.ofCodes A (fun p => tupleRV M p.1) codes hCodes hDom ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode ⟨codes c.val,hDom c⟩).trans (hCode c).symm

theorem vfLeadingTermMap_at (A : DefSet (rawMixedSpace (M := M) n r) S) (p : A) :
    (vfLeadingTermMap A p).val = tupleRV M p.val.1 := rfl

def pureRVTagDomain (A : DefSet (rawMixedSpace (M := M) n r) S) := (rvTailMap A).image

def pureRVTagQuotient (A : DefSet (rawMixedSpace (M := M) n r) S) : Map A (pureRVTagDomain A) :=
  (rvTailMap A).toImage

theorem pureRVTagQuotient_surjective (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Function.Surjective (pureRVTagQuotient A) := by
  rintro ⟨_,p,rfl⟩
  exact ⟨p,rfl⟩

theorem pureRVTagQuotient_eq_iff (A : DefSet (rawMixedSpace (M := M) n r) S) (p q : A) :
    pureRVTagQuotient A p = pureRVTagQuotient A q ↔ p.val.2 = q.val.2 :=
  ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

def preparedRVVolume (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    Map (pureRVTagDomain A) (DefSet.univ (rawRVSpace (M := M) n) S) :=
  definableSurjectiveDescent (pureRVTagQuotient A) (pureRVTagQuotient_surjective A) (vfLeadingTermMap A)
    (fun p q he => Subtype.ext (hTag p.val p.property q.val q.property ((pureRVTagQuotient_eq_iff A p q).mp he)))

theorem preparedRVVolume_at (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) (p : A) :
    (preparedRVVolume A hTag (pureRVTagQuotient A p)).val = tupleRV M p.val.1 :=
  congrArg Subtype.val (definableSurjectiveDescent_apply _ _ _ _ p)

def preparedRVObject (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) : RVObject (M := M) S n where
  arity := r
  domain := pureRVTagDomain A
  volume := preparedRVVolume A hTag

end DiamondIntegral.Section6
