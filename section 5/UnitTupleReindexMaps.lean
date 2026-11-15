import «section 5».NativeRVSetArithmetic
import «section 3».GammaGroundBijections

/-! Actual original-ground coordinate substitutions on nonzero RV tuples. -/
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

def unitTupleReindexMap (S : Set M) {n m : ℕ} (f : Fin m → Fin n) :
    Map (DefSet.univ (rawRVUnitSpace (M := M) n) S) (DefSet.univ (rawRVUnitSpace (M := M) m) S) := by
  have hdom (c : (rawRVUnitSpace (M := M) n).domain) :
      (c.val ∘ f) ∈ (rawRVUnitSpace (M := M) m).domain := by
    apply (Set.ext_iff.mp rvUnitValues_range _).mpr
    exact fun j => (Set.ext_iff.mp rvUnitValues_range c.val).mp c.property (f j)
  refine Map.ofCodes _ (fun u => u ∘ f) (fun c => c ∘ f)
    (fun _ => Set.DefinableFun.proj LRV) hdom ?_
  intro c
  apply rvUnitValues_injective
  funext j
  exact (congrFun (rvUnitValues_decode ⟨c.val ∘ f,hdom c⟩) j).trans
    (congrFun (rvUnitValues_decode c) (f j)).symm

def groundUnitTupleReindexMap {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
    {n m : ℕ} (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (f : Fin m → Fin n) :=
  GammaGroundMap.ofGlobal A (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) m))
    (unitTupleReindexMap B.real f) (fun _ => Set.mem_univ _)

theorem unitTupleReindexMap_value (S : Set M) {n m : ℕ} (f : Fin m → Fin n)
    (u : DefSet.univ (rawRVUnitSpace (M := M) n) S) :
    (unitTupleReindexMap S f u).val = u.val ∘ f := rfl

def groundUnitTuplePermutationBijection {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
    {n : ℕ} (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (σ : Equiv.Perm (Fin n)) :
    GammaGroundBijection A (groundUnitTupleReindexMap A σ).image :=
  ⟨(groundUnitTupleReindexMap A σ).toImage,
    (groundUnitTupleReindexMap A σ).toImage_bijective (by
      intro a b he
      apply Subtype.ext
      have hab : a.val ∘ σ = b.val ∘ σ := congrArg Subtype.val he
      funext i
      simpa only [Function.comp_def,σ.apply_symm_apply] using congrFun hab (σ.symm i))⟩

end DiamondIntegral.Section5
