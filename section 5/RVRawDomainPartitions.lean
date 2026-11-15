import «section 5».OriginalRVRowObjects

/-! Literal raw-code domains retain complete finite disjoint partitions
of actual native RV domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {a : ℕ}

theorem rawDomain_finite_partition {ι : Type} [Fintype ι]
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (A : ι → GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    (∀ i j, i ≠ j → Disjoint (rawDomain (A i)) (rawDomain (A j))) ∧
      ∀ v, v ∈ rawDomain X ↔ ∃ i, v ∈ rawDomain (A i) := by
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro v ⟨x,hx,hex⟩ ⟨y,hy,hey⟩
    have he : x = y := rvValues_injective (hex.trans hey.symm)
    exact Set.disjoint_left.mp (hd i j hij) hx (he.symm ▸ hy)
  · intro v
    constructor
    · rintro ⟨x,hx,he⟩
      obtain ⟨i,hi⟩ := (hcov x).mp hx
      exact ⟨i,x,hi,he⟩
    · rintro ⟨i,x,hx,he⟩
      exact ⟨x,(hcov x).mpr ⟨i,hx⟩,he⟩

end DiamondIntegral.Section5
