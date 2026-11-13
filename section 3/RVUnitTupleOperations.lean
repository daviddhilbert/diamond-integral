import «section 3».RVUnitSpace
import «section 3».GammaGroundMapProducts
import «section 3».GammaGroundMapImages
import «section 3».RVUnitValueHom
import «section 3».RVAngularQuotient
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

/-- Coordinate multiplication on RV-unit tuples has its parameter-free
code graph, without choosing a lift of any Gamma point. -/
def rvUnitTupleMulMap (S : Set M) (n : ℕ) :
    Map (DefSet.univ ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace n)) S)
      (DefSet.univ (rawRVUnitSpace n) S) := by
  let F (z : Fin n ⊕ Fin n → M) : Fin n → M :=
    fun i => iRVMul (z (.inl i)) (z (.inr i))
  have hF : S.DefinableMap LRV F := by
    intro i
    exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
        (show S.DefinableMap LRV (fun z : Fin n ⊕ Fin n → M => ![z (.inl i),z (.inr i)]) from
          fun j => by fin_cases j <;> exact Set.DefinableFun.proj LRV)
  have hc (c : ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace n)).domain) :
      F c.val = rvUnitValues
        (fun i => ((rawRVUnitSpace n).decode ⟨c.val ∘ Sum.inl,c.property.1⟩ i) *
          ((rawRVUnitSpace n).decode ⟨c.val ∘ Sum.inr,c.property.2⟩ i)) := by
    let x : Fin n → (CanonicalRV.RVSort M)ˣ := (rawRVUnitSpace n).decode ⟨c.val ∘ Sum.inl,c.property.1⟩
    let y : Fin n → (CanonicalRV.RVSort M)ˣ := (rawRVUnitSpace n).decode ⟨c.val ∘ Sum.inr,c.property.2⟩
    funext i
    have hx := congrFun (rvUnitValues_decode (M := M) ⟨c.val ∘ Sum.inl,c.property.1⟩) i
    have hy := congrFun (rvUnitValues_decode (M := M) ⟨c.val ∘ Sum.inr,c.property.2⟩) i
    change iRVMul (c.val (.inl i)) (c.val (.inr i)) =
      (((x i : CanonicalRV.RVSort M) * (y i : CanonicalRV.RVSort M))).val
    change (x i).val.val = c.val (.inl i) at hx
    change (y i).val.val = c.val (.inr i) at hy
    rw [← hx,← hy]
    exact (RVOperations.mul_val _ _).symm
  have hd (c : ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace n)).domain) :
      F c.val ∈ (rawRVUnitSpace (M := M) n).domain := ⟨_,(hc c).symm⟩
  refine Map.ofCodes _ (fun p : (Fin n → (CanonicalRV.RVSort M)ˣ) × (Fin n → (CanonicalRV.RVSort M)ˣ) => fun i => p.1 i * p.2 i) F hF hd ?_
  intro c
  apply rvUnitValues_injective
  exact (rvUnitValues_decode _).trans (hc c)

def gammaGroundRVUnitTupleMulMap {hc : CanonicalStructure.IsCanonical (M := M)}
    {B : GammaParameters.Base (M := M)}
    (A : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace n))) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)) :=
  GammaGroundMap.ofGlobal _ _ (rvUnitTupleMulMap B.real n) (fun _ => Set.mem_univ _)

@[simp] theorem gammaGroundRVUnitTupleMulMap_value {hc : CanonicalStructure.IsCanonical (M := M)}
    {B : GammaParameters.Base (M := M)}
    (A : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace n))) (a : A) :
    (gammaGroundRVUnitTupleMulMap A a).val =
      (fun i => a.val.1 i * a.val.2 i) := rfl

theorem rvUnitTupleValues_mul (a b : Fin n → (CanonicalRV.RVSort M)ˣ) :
    rvUnitTupleValues (a*b) = rvUnitTupleValues a * rvUnitTupleValues b := by
  funext i
  exact (rvUnitValueHom (M := M)).map_mul (a i) (b i)

theorem rvUnitTupleValues_inv (a : Fin n → (CanonicalRV.RVSort M)ˣ) :
    rvUnitTupleValues (a⁻¹) = (rvUnitTupleValues a)⁻¹ := by
  funext i
  exact (rvUnitValueHom (M := M)).map_inv (a i)
end DiamondIntegral.Section3
