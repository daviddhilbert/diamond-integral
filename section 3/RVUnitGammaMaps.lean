import «section 3».RVAngularQuotient
import «section 3».RVUnitSpace
import «section 3».GammaVolumeForms
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem rvUnitValueHom_surjective : Function.Surjective (rvUnitValueHom (M := M)) := by
  intro γ
  let c := representative γ
  let x : (CanonicalRV.RVSort M)ˣ := Units.mk0 c.val (fun h => c.property ((congrArg Subtype.val h).trans RVOperations.zero_val))
  exact ⟨x,representative_value γ⟩

theorem rvUnitTupleValues_surjective (m : ℕ) : Function.Surjective (rvUnitTupleValues (M := M) (m := m)) := by
  intro γ
  choose x hx using fun i : Fin m => rvUnitValueHom_surjective (γ i)
  exact ⟨x,funext hx⟩

/-- Actual full-code projection from nonzero RV tuples to Gamma tuples.
The definable graph includes every target representative. -/
def rvUnitGammaMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (m : ℕ) :
    Map (DefSet.univ (rawRVUnitSpace (M := M) m) S)
      (DefSet.univ ((volumeGammaSpace hc).power (Fin m)) S) := by
  let F (z : Fin m → M) : Fin m × Fin 1 → M := fun ij => z ij.1
  have hNZ (c : (rawRVUnitSpace (M := M) m).domain) : ∀ i, NonzeroRV (c.val i) :=
    (Set.ext_iff.mp rvUnitValues_range c.val).mp c.property
  have hdom (c : (rawRVUnitSpace (M := M) m).domain) :
      F c.val ∈ ((volumeGammaSpace hc).power (Fin m)).domain := fun i => hNZ c i
  refine Map.ofCodes _ rvUnitTupleValues F (fun _ => Set.DefinableFun.proj LRV) hdom ?_
  intro c
  funext i
  apply Subtype.ext
  change Values.vrv ⟨c.val i,(hNZ c i).1⟩ = Values.vrv (((rawRVUnitSpace m).decode c i : (CanonicalRV.RVSort M)ˣ) : CanonicalRV.RVSort M)
  exact congrArg Values.vrv (Subtype.ext (congrFun (rvUnitValues_decode c) i).symm)

theorem rvUnitGammaMap_values (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (m : ℕ)
    (x : DefSet.univ (rawRVUnitSpace (M := M) m) S) :
    (rvUnitGammaMap hc S m x).val = rvUnitTupleValues x.val := rfl
end DiamondIntegral.Section3
