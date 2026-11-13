import «section 3».RVUnitMixedRectangles
import «section 3».FullGammaPresentations
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

def rvUnitSetOfRaw (W : Set (Fin n → M)) (hW : DefinableOver S (fun _ => .rv) W) :
    DefSet (rawRVUnitSpace (M := M) n) S :=
  ⟨{x | rvUnitValues x ∈ W},rvUnitSpace_predicate_definable S _ (fun z => z ∈ W) hW.raw_definable (fun _ => Iff.rfl)⟩

def rvUnitGammaPreimage (hc : CanonicalStructure.IsCanonical (M := M))
    (G : DefSet ((volumeGammaSpace hc).power (Fin m)) S) :
    DefSet (rawRVUnitSpace (M := M) m) S := by
  refine ⟨{x | rvUnitTupleValues x ∈ G.carrier},?_⟩
  have hh := (rvUnitGammaMap hc S m).definable_preimage G.definable
  have he : {x | ∃ a : DefSet.univ (rawRVUnitSpace (M := M) m) S, a.val = x ∧ rvUnitTupleValues a.val ∈ G.carrier} =
      {x | rvUnitTupleValues x ∈ G.carrier} := by
    ext x
    exact ⟨fun ⟨a,ha,hg⟩ => ha ▸ hg,fun hx => ⟨⟨x,Set.mem_univ _⟩,rfl,hx⟩⟩
  change (rawRVUnitSpace (M := M) m).Definable S {x | ∃ a : DefSet.univ (rawRVUnitSpace (M := M) m) S, a.val = x ∧ rvUnitTupleValues a.val ∈ G.carrier} at hh
  rw [he] at hh
  exact hh

/-- Finite disjoint product factors are actual definable sets over the
same real base, with finite Gamma support on the residue factors. -/
theorem rvUnitMixed_definable_products {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hsmall : Cardinal.mk S < κ) (hΓ : Section2.NontrivialDefinableGamma (⟨S,∅⟩ : Base (M := M)))
    (T : DefSet ((rawRVUnitSpace (M := M) n).prod ((volumeGammaSpace hc).power (Fin m))) S)
    (A : DefSet (rawRVUnitSpace (M := M) n) S)
    (hA : (rvUnitTupleValues '' A.carrier).Finite)
    (hsub : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ A.carrier) :
    ∃ N : ℕ, ∃ R : Fin N → DefSet (rawRVUnitSpace (M := M) n) S,
      ∃ G : Fin N → DefSet ((volumeGammaSpace hc).power (Fin m)) S,
      (∀ i, (rvUnitTupleValues '' (R i).carrier).Finite) ∧
      (∀ i j, i ≠ j → Disjoint (R i).carrier (R j).carrier) ∧
      ∀ x γ, (x,γ) ∈ T.carrier ↔ ∃ i, x ∈ (R i).carrier ∧ γ ∈ (G i).carrier := by
  obtain ⟨P,hP,hdis,hcov⟩ := rvUnitMixed_finite_rectangles hκ hs h00 hc hsmall hΓ T A hA hsub
  let e : Fin (Fintype.card P) ≃ P := (Fintype.equivFin P).symm
  let R : Fin (Fintype.card P) → DefSet (rawRVUnitSpace (M := M) n) S := fun i =>
    rvUnitSetOfRaw (e i).val (hP _ (e i).property).2.2.1
  let G : Fin (Fintype.card P) → DefSet ((volumeGammaSpace hc).power (Fin m)) S := fun i =>
    gammaPowerSetOfFull hc (fun γ => γ ∈ gammaTupleFamilyValues (rvUnitMixedRelation T) (e i).val)
      (hP _ (e i).property).2.2.2
  have hRA : ∀ i, (R i).carrier ⊆ A.carrier := by
    intro i x hx
    obtain ⟨y,hy,he⟩ := (hP _ (e i).property).2.1 hx
    exact rvUnitValues_injective he ▸ hy
  refine ⟨Fintype.card P,R,G,fun i => hA.subset (Set.image_mono (hRA i)),?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hne : (e i).val ≠ (e j).val := fun he => hij (e.injective (Subtype.ext he))
    exact Set.disjoint_left.mp (hdis (e i).property (e j).property hne) hi hj
  · intro x γ
    rw [hcov x γ]
    constructor
    · rintro ⟨W,hW,hx,hγ⟩
      obtain ⟨i,hi⟩ := e.surjective ⟨W,hW⟩
      refine ⟨i,?_,?_⟩
      · change rvUnitValues x ∈ (e i).val
        simpa only [hi] using hx
      · change γ ∈ gammaTupleFamilyValues (rvUnitMixedRelation T) (e i).val
        simpa only [hi] using hγ
    · rintro ⟨i,hx,hγ⟩
      exact ⟨(e i).val,(e i).property,hx,hγ⟩
end DiamondIntegral.Section3
