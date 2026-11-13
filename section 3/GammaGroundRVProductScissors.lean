import «section 3».GammaGroundRVProducts
import «section 3».GammaGroundCarrierBijections
import «section 3».GammaGroundRVGradedMonoid

/-! Products preserve actual same-ground cuts and disjoint partitions. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n m k l : ℕ}

theorem GammaGroundDefSet.eq_of_carrier_eq {Q : Space LRV M} {A B : GammaGroundDefSet hc ground Q}
    (h : A.carrier = B.carrier) : A = B := by
  cases A
  cases B
  cases h
  rfl

theorem mem_gammaGroundRVProductDomain (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) (t : Fin (n + m) → CanonicalRV.RVSort M) :
    t ∈ (gammaGroundRVProductDomain A B).carrier ↔
      ∃ a ∈ A.carrier, ∃ b ∈ B.carrier, rvAppend a b = t := by
  constructor
  · rintro ⟨p, he⟩
    exact ⟨p.val.1, p.property.1, p.val.2, p.property.2, he⟩
  · rintro ⟨a, ha, b, hb, he⟩
    exact ⟨⟨(a, b), ha, hb⟩, he⟩

theorem gammaGroundRVProductDomain_union (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (B C : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) :
    gammaGroundRVProductDomain A (B.union C) = (gammaGroundRVProductDomain A B).union (gammaGroundRVProductDomain A C) := by
  apply GammaGroundDefSet.eq_of_carrier_eq
  ext t
  constructor
  · intro ht
    obtain ⟨a, ha, b, hb | hb, he⟩ := (mem_gammaGroundRVProductDomain A (B.union C) t).mp ht
    · exact Or.inl ((mem_gammaGroundRVProductDomain A B t).mpr ⟨a, ha, b, hb, he⟩)
    · exact Or.inr ((mem_gammaGroundRVProductDomain A C t).mpr ⟨a, ha, b, hb, he⟩)
  · rintro (ht | ht)
    · obtain ⟨a, ha, b, hb, he⟩ := (mem_gammaGroundRVProductDomain A B t).mp ht
      exact (mem_gammaGroundRVProductDomain A (B.union C) t).mpr ⟨a, ha, b, Or.inl hb, he⟩
    · obtain ⟨a, ha, b, hb, he⟩ := (mem_gammaGroundRVProductDomain A C t).mp ht
      exact (mem_gammaGroundRVProductDomain A (B.union C) t).mpr ⟨a, ha, b, Or.inr hb, he⟩

theorem gammaGroundRVProductDomain_disjoint (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (B C : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) (hd : Disjoint B.carrier C.carrier) :
    Disjoint (gammaGroundRVProductDomain A B).carrier (gammaGroundRVProductDomain A C).carrier := by
  apply Set.disjoint_left.mpr
  intro t hB hC
  obtain ⟨a, ha, b, hb, heb⟩ := (mem_gammaGroundRVProductDomain A B t).mp hB
  obtain ⟨a', ha', c, hc, hec⟩ := (mem_gammaGroundRVProductDomain A C t).mp hC
  have he : (a, b) = (a', c) := by
    apply rvAppend_injective
    exact heb.trans hec.symm
  have hbc : b = c := congrArg Prod.snd he
  exact Set.disjoint_left.mp hd hb (hbc.symm ▸ hc)

theorem gammaGroundRVProductRestrictionSubset (U : GammaGroundRVObject hc ground k) (V : GammaGroundRVObject hc ground l)
    (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) V.arity)) (hB : B.carrier ⊆ V.domain.carrier) :
    (gammaGroundRVProductDomain U.domain B).carrier ⊆ (U.product V).domain.carrier := by
  intro t ht
  obtain ⟨a, ha, b, hb, he⟩ := (mem_gammaGroundRVProductDomain U.domain B t).mp ht
  exact (mem_gammaGroundRVProductDomain U.domain V.domain t).mpr ⟨a, ha, b, hB hb, he⟩


def gammaGroundRVProductRestrictionIso (U : GammaGroundRVObject hc ground k) (V : GammaGroundRVObject hc ground l)
    (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) V.arity)) (hB : B.carrier ⊆ V.domain.carrier) :
    U.product (V.restrict B hB) ≅ (U.product V).restrict (gammaGroundRVProductDomain U.domain B)
      (gammaGroundRVProductRestrictionSubset U V B hB) :=
  asIso (show _ ⟶ _ from GammaGroundBijection.id (gammaGroundRVProductDomain U.domain B))

theorem gammaGroundRVClass_partition (U : GammaGroundRVObject hc ground k)
    (A B : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.arity))
    (hA : A.carrier ⊆ U.domain.carrier) (hB : B.carrier ⊆ U.domain.carrier)
    (hd : Disjoint A.carrier B.carrier) (he : (A.union B).carrier = U.domain.carrier) :
    gammaGroundRVClass U = gammaGroundRVClass (U.restrict A hA) + gammaGroundRVClass (U.restrict B hB) := by
  have hdiff : (U.domain.sdiff A).carrier = B.carrier := by
    ext a
    constructor
    · rintro ⟨ha, hn⟩
      exact (he.ge ha).resolve_left hn
    · intro hb
      exact ⟨hB hb, fun ha => Set.disjoint_left.mp hd ha hb⟩
  have hcut := gammaGroundRVClass_scissor U A hA
  have hi : U.restrict (U.domain.sdiff A) (fun _ h => h.1) ≅ U.restrict B hB :=
    asIso (show _ ⟶ _ from GammaGroundBijection.ofCarrierEq hdiff)
  rw [gammaGroundRVClass_iso hi] at hcut
  exact hcut.symm

end DiamondIntegral.Section3
