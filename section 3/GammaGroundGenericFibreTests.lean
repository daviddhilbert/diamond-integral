import «section 3».GammaGroundRVGenericValueImage
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {κ : Cardinal} {hc : CanonicalStructure.IsCanonical (M := M)}
variable (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
variable (hsmall : Cardinal.mk B.real < κ) {n : ℕ}

/-- A single actual point of any prescribed full value fibre tests all
members of a finite family for generic membership simultaneously. -/
theorem gammaGroundGeneric_finite_fibre_test (hκ : Cardinal.aleph0 < κ)
    {ι : Type} [Finite ι] (A : ι → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (γ : Fin n → Values.Gamma (M := M)) :
    ∃ u : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitTupleValues u = γ ∧
      ∀ j, (γ ∈ (gammaGroundRVGenericValueImage hs h00 B hsmall (A j)).carrier ↔ u ∈ (A j).carrier) := by
  obtain ⟨a,ha⟩ := rvUnitTupleValues_surjective (M := M) n γ
  have hA (j : ι) := (gammaGroundRVUnit_definable_iff (A j).carrier).mp (A j).definable
  obtain ⟨E,x,_,_,_,hx0,htest⟩ := exists_rvGeneric_family_test_point hc hκ hs h00 B hsmall
    (fun j => rvUnitValues '' (A j).carrier) hA (fun _ => a) (List.finRange n)
  let u : Fin n → (CanonicalRV.RVSort M)ˣ := fun i => a i * residueUnitToRV (Units.mk0 (x i) (hx0 i))
  have hval : rvUnitTupleValues u = γ := by
    have he : rvUnitTupleValues u = rvUnitTupleValues a := by
      funext i
      simp only [rvUnitTupleValues,u,map_mul,residueUnitToRV_value_one,mul_one]
    exact he.trans ha
  have hraw : rvUnitValues u = rvNormalizedTuple a x := rfl
  refine ⟨u,hval,?_⟩
  intro j
  have hg := gammaGroundRVGenericValueImage_mem_iff hs h00 B hsmall (A j) u
  rw [hval,hraw] at hg
  have hm : rvNormalizedTuple a x ∈ rvUnitValues '' (A j).carrier ↔ u ∈ (A j).carrier := by
    rw [← hraw]
    simp only [Set.mem_image,rvUnitValues_injective.eq_iff,exists_eq_right]
  exact hg.trans ((htest j).trans hm)

/-- Fibrewise inclusion suffices for monotonicity of generic value
images. Inclusion outside the specified fibre is unnecessary. -/
theorem gammaGroundGeneric_mono_on_fibre (hκ : Cardinal.aleph0 < κ)
    (A C : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (γ : Fin n → Values.Gamma (M := M))
    (hsub : ∀ u : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitTupleValues u = γ → u ∈ A.carrier → u ∈ C.carrier) :
    γ ∈ (gammaGroundRVGenericValueImage hs h00 B hsmall A).carrier →
      γ ∈ (gammaGroundRVGenericValueImage hs h00 B hsmall C).carrier := by
  let F : Bool → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) := fun b => if b then C else A
  obtain ⟨u,hu,hF⟩ := gammaGroundGeneric_finite_fibre_test hs h00 B hsmall hκ F γ
  intro hA
  exact (hF true).mpr (hsub u hu ((hF false).mp hA))

end DiamondIntegral.Section3
