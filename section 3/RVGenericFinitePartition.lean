import «section 3».RVGenericFamilyPoint
import «section 3».RVUnitGammaMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem rvUnitTuples_same_of_values_eq {n : ℕ}
    (u v : Fin n → (CanonicalRV.RVSort M)ˣ)
    (h : rvUnitTupleValues u = rvUnitTupleValues v) : Same (rvUnitValues u) (rvUnitValues v) := by
  intro i
  have hu : NonzeroRV (u i).val.val := ⟨(u i).val.property,by
    intro hz
    exact Units.ne_zero (u i) (Subtype.ext (hz.trans RVOperations.zero_val.symm))⟩
  have hv : NonzeroRV (v i).val.val := ⟨(v i).val.property,by
    intro hz
    exact Units.ne_zero (v i) (Subtype.ext (hz.trans RVOperations.zero_val.symm))⟩
  have he : Values.vrv (u i).val = Values.vrv (v i).val := congrArg Subtype.val (congrFun h i)
  have hs := (Values.vrv_eq_iff _ _).mp he
  exact ⟨hu,hv,hs.1,hs.2⟩

/-- A finite definable partition of one full RV fibre has a unique
generic part. Its uniform selector is constant on the entire full fibre,
not merely on a chosen residual open subset. -/
theorem rvFullFibreGeneric_partition {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) {n : ℕ} {ι : Type} [Finite ι]
    (A : ι → Set (Fin n → M)) (hA : ∀ j, DefinableOverBase B (fun _ => .rv) (A j))
    (a : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hpart : ∀ u : Fin n → (CanonicalRV.RVSort M)ˣ,
      rvUnitTupleValues u = rvUnitTupleValues a → ∃! j, rvUnitValues u ∈ A j) :
    ∃! j, ∀ u : Fin n → (CanonicalRV.RVSort M)ˣ,
      rvUnitTupleValues u = rvUnitTupleValues a → rvUnitValues u ∈ rvFullFibreGeneric (A j) := by
  obtain ⟨E,x,_,_,_,hx0,htest⟩ := exists_rvGeneric_family_test_point hc hκ hs h00 B hsmall
    A hA (fun _ => a) (List.finRange n)
  let u : Fin n → (CanonicalRV.RVSort M)ˣ := fun i => a i * residueUnitToRV (Units.mk0 (x i) (hx0 i))
  have hval : rvUnitTupleValues u = rvUnitTupleValues a := by
    funext i
    simp only [rvUnitTupleValues,u,map_mul,residueUnitToRV_value_one,mul_one]
  have hraw : rvUnitValues u = rvNormalizedTuple a x := rfl
  have ht (j : ι) : rvUnitValues u ∈ rvFullFibreGeneric (A j) ↔ rvUnitValues u ∈ A j := by
    rw [hraw]
    exact htest j
  obtain ⟨j,hj,hjuniq⟩ := hpart u hval
  refine ⟨j,?_,?_⟩
  · intro v hv
    have hsame := rvUnitTuples_same_of_values_eq u v (hval.trans hv.symm)
    exact (rvFullFibreGeneric_invariant (A j) _ _ hsame).mp ((ht j).mpr hj)
  · intro k hk
    exact hjuniq k ((ht k).mp (hk u hval))

end DiamondIntegral.Section3
