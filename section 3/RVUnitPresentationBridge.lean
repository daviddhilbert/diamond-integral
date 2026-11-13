import «section 3».RVUnitSpace
import «section 3».DefinableBijections
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def rvUnitToRVMap (X : DefSet (rawRVUnitSpace (M := M) n) S) :
    Map X (DefSet.univ (rawRVSpace n) S) := by
  let f (x : Fin n → (CanonicalRV.RVSort M)ˣ) := fun i => (x i : CanonicalRV.RVSort M)
  have hdom (c : (rawRVUnitSpace (M := M) n).domain) : c.val ∈ (rawRVSpace (M := M) n).domain := by
    obtain ⟨x,hx⟩ := c.property
    exact ⟨f x,hx⟩
  refine Map.ofCodes X f id (fun _ => Set.DefinableFun.proj LRV) hdom ?_
  intro c
  exact rvValues_injective ((rvValues_decode ⟨c.val,hdom c⟩).trans (rvUnitValues_decode c).symm)

theorem rvUnitToRVMap_values (X : DefSet (rawRVUnitSpace (M := M) n) S) (a : X) :
    (rvUnitToRVMap X a).val = fun i => (a.val i : CanonicalRV.RVSort M) := rfl

theorem rvUnitToRVMap_injective (X : DefSet (rawRVUnitSpace (M := M) n) S) :
    Function.Injective (rvUnitToRVMap X) := by
  intro a b he
  apply Subtype.ext
  funext i
  apply Units.ext
  exact congrArg (fun z => z.val i) he

def rvUnitPresentationBijection (X : DefSet (rawRVUnitSpace (M := M) n) S) :
    DefinableBijection X (rvUnitToRVMap X).image where
  map := (rvUnitToRVMap X).toImage
  bijective := by
    constructor
    · intro a b he
      apply rvUnitToRVMap_injective X
      have hv : (rvUnitToRVMap X a).val = (rvUnitToRVMap X b).val :=
        congrArg (fun z : (rvUnitToRVMap X).image => z.val) he
      exact Subtype.ext hv
    · rintro ⟨y,a,ha⟩
      exact ⟨a,Subtype.ext ha⟩
end DiamondIntegral.Section3
