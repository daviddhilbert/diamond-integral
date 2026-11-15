import «section 5».RVGammaReverseLifts

/-! Reversed Gamma-code lifts and the literal ordered lifts have the
same native value through an actual original-ground permutation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

theorem reverseSuffixPermutation_involutive : Function.Involutive (reverseSuffixPermutation p n) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [reverseSuffixPermutation_left,reverseSuffixPermutation_left]
  · rw [reverseSuffixPermutation_right,reverseSuffixPermutation_right,Fin.rev_rev]

theorem rvGammaLift_reindex_mem
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (u : Fin (p+n) → (CanonicalRV.RVSort M)ˣ) :
    (u ∘ reverseSuffixPermutation p n) ∈ (rvGammaFamilyLift T).carrier ↔ u ∈ (rvGammaReverseLift T).carrier := by
  change ((u ∘ reverseSuffixPermutation p n) ∘ Fin.castAdd n,
    rvUnitTupleValues ((u ∘ reverseSuffixPermutation p n) ∘ Fin.natAdd p)) ∈ T.carrier ↔ _
  have hl : (u ∘ reverseSuffixPermutation p n) ∘ Fin.castAdd n = u ∘ Fin.castAdd n := by
    funext j; simp only [Function.comp_def,reverseSuffixPermutation_left]
  have hr : (u ∘ reverseSuffixPermutation p n) ∘ Fin.natAdd p = u ∘ Fin.natAdd p ∘ Fin.rev := by
    funext j; simp only [Function.comp_def,reverseSuffixPermutation_right]
  rw [hl,hr]
  rfl

def rvGammaReverseBijection
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))) :
    GammaGroundBijection (rvGammaReverseLift T) (rvGammaFamilyLift T) := by
  let f : GammaGroundMap (rvGammaReverseLift T) (rvGammaFamilyLift T) :=
    GammaGroundMap.ofGlobal _ _ (unitTupleReindexMap B.real (reverseSuffixPermutation p n))
      (fun u => (rvGammaLift_reindex_mem T u.val).mpr u.property)
  refine ⟨f,?_,?_⟩
  · intro u v he
    have huv : u.val ∘ reverseSuffixPermutation p n = v.val ∘ reverseSuffixPermutation p n := congrArg Subtype.val he
    apply Subtype.ext
    funext i
    simpa only [Function.comp_def,reverseSuffixPermutation_involutive i] using
      congrFun huv (reverseSuffixPermutation p n i)
  · intro v
    have hu : (v.val ∘ reverseSuffixPermutation p n) ∈ (rvGammaReverseLift T).carrier := by
      apply (rvGammaLift_reindex_mem T _).mp
      have he : (v.val ∘ reverseSuffixPermutation p n) ∘ reverseSuffixPermutation p n = v.val := by
        funext i; simp only [Function.comp_def,reverseSuffixPermutation_involutive i]
      exact he.symm ▸ v.property
    refine ⟨⟨v.val ∘ reverseSuffixPermutation p n,hu⟩,?_⟩
    apply Subtype.ext
    funext i
    exact congrArg v.val (reverseSuffixPermutation_involutive i)

theorem rvGammaReverseLift_finite_partition {ι : Type} [Fintype ι]
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (A : ι → GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x γ, (x,γ) ∈ T.carrier ↔ ∃ i, (x,γ) ∈ (A i).carrier) :
    (∀ i j, i ≠ j → Disjoint (rvGammaReverseLift (A i)).carrier (rvGammaReverseLift (A j)).carrier) ∧
      ∀ u, u ∈ (rvGammaReverseLift T).carrier ↔ ∃ i, u ∈ (rvGammaReverseLift (A i)).carrier := by
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro u hi hj
    exact Set.disjoint_left.mp (hd i j hij) hi hj
  · intro u
    exact hcov (u ∘ Fin.castAdd n) (rvUnitTupleValues (u ∘ Fin.natAdd p ∘ Fin.rev))

end DiamondIntegral.Section5
