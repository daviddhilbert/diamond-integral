import «section 3».GammaGroundFiniteValuePoints
import «section 3».GammaGroundRVUnitProducts
import «section 3».GammaGroundMapImages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem fullGamma_tuple_singleton_definable (δ : Fin n → Values.Gamma (M := M))
    (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i)) :
    FullGammaSyntax.Definable (integrationGammaBase B) (fun γ => γ = δ) := by
  apply (FullGammaSyntax.Definable.forall_finite (fun i : Fin n =>
    FullGammaSyntax.unary_at (integrationGammaDefinable (hδ i)) i)).congr
  intro γ
  exact funext_iff.symm

def gammaGroundRVUnitValueFibre
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (δ : Fin n → Values.Gamma (M := M)) (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i)) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) :=
  ⟨{r | r ∈ R.carrier ∧ rvUnitTupleValues r = δ},R.definable.inter
    ((gammaGroundGammaPower_predicate_definable _ (fullGamma_tuple_singleton_definable δ hδ)).preimage
      (rvUnitGammaMap hc B.real n))⟩

/-- Finite value support splits into individual, original-ground
definable value fibres. No RV representative is added to the ground. -/
theorem gammaGroundRVUnit_finite_value_fibres
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hfin : (rvUnitTupleValues '' R.carrier).Finite) :
    ∃ N : ℕ, ∃ δ : Fin N → Fin n → Values.Gamma (M := M),
      ∃ Q : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n),
      (∀ j i, GammaDefinableClosureAtBase B (δ j i)) ∧
      (∀ j, (Q j).carrier = {r | r ∈ R.carrier ∧ rvUnitTupleValues r = δ j}) ∧
      (∀ j k, j ≠ k → Disjoint (Q j).carrier (Q k).carrier) ∧
      (∀ r, r ∈ R.carrier ↔ ∃ j, r ∈ (Q j).carrier) := by
  let v := GammaGroundMap.ofGlobal R (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n)))
    (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)
  have he : v.image.carrier = rvUnitTupleValues '' R.carrier := by
    ext γ
    exact ⟨fun ⟨r,hr⟩ => ⟨r.val,r.property,hr⟩,fun ⟨r,hr,he⟩ => ⟨⟨r,hr⟩,he⟩⟩
  have hf : v.image.carrier.Finite := he ▸ hfin
  letI : Fintype v.image := hf.fintype
  let e : Fin (Fintype.card v.image) ≃ v.image := (Fintype.equivFin v.image).symm
  let δ := fun j => (e j).val
  have hd : ∀ j i, GammaDefinableClosureAtBase B (δ j i) := fun j =>
    gammaGroundGamma_finite_tuple_point_definable v.image hf (δ j) (e j).property
  let Q := fun j => gammaGroundRVUnitValueFibre R (δ j) (hd j)
  refine ⟨Fintype.card v.image,δ,Q,hd,fun _ => rfl,?_,?_⟩
  · intro j k hjk
    apply Set.disjoint_left.mpr
    rintro r ⟨_,hj⟩ ⟨_,hk⟩
    exact hjk (e.injective (Subtype.ext (hj.symm.trans hk)))
  · intro r
    constructor
    · intro hr
      have hv : rvUnitTupleValues r ∈ v.image.carrier := he.symm ▸ Set.mem_image_of_mem _ hr
      obtain ⟨j,hj⟩ := e.surjective ⟨rvUnitTupleValues r,hv⟩
      exact ⟨j,hr,(congrArg Subtype.val hj).symm⟩
    · rintro ⟨j,hj⟩
      exact hj.1
end DiamondIntegral.Section3
