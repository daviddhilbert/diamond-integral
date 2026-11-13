import «section 3».RVUnitGammaFormGraph
import «section 3».RVGammaFiniteFunctionCover
import «section 3».FullGammaFunctionMaps
import «section 3».GammaGroundFiniteCoverPartition
import «section 3».GammaGroundEqualizers
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- Actual same-ground disjoint source cells on which a Gamma-valued
volume map is one Gamma function of the original coordinate values. -/
theorem gammaGroundRVUnitGammaForm_value_partition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (w : GammaGroundMap A (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    ∃ J : ℕ, ∃ Q : Fin J → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n),
      ∃ f : Fin J → GammaValueFunctionData B n,
      (∀ j, (Q j).carrier ⊆ A.carrier) ∧
      (∀ i j, i ≠ j → Disjoint (Q i).carrier (Q j).carrier) ∧
      (∀ x, x ∈ A.carrier ↔ ∃ j, x ∈ (Q j).carrier) ∧
      ∀ j (a : A), a.val ∈ (Q j).carrier → (f j).val (rvUnitTupleValues a.val) = (w a).val := by
  obtain ⟨N,f,hf⟩ := rvUnitGammaGraph_finite_value_functions hκ hs h00 hc B hsmall hγsmall
    A.carrier (fun a => (w a).val) (gammaGroundRVUnitGammaForm_graph A w)
  let v : GammaGroundMap A (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n))) :=
    GammaGroundMap.ofGlobal _ _ (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)
  let ψ := fun i => (fullGammaFunctionMap (f i).val (f i).property).comp v
  let E := fun i => w.equalizer (ψ i)
  have hcover : ∀ x ∈ A.carrier, ∃ i, x ∈ (E i).carrier := by
    intro x hx
    let a : A := ⟨x,hx⟩
    obtain ⟨i,hi⟩ := hf a
    exact ⟨i,a,rfl,hi.symm⟩
  obtain ⟨J,Q,hQ,hdis,hcov⟩ := gammaGround_finite_cover_partition A E hcover
  have hchoice : ∀ j, ∃ F : GammaValueFunctionData B n,
      ∀ a : A, a.val ∈ (Q j).carrier → F.val (rvUnitTupleValues a.val) = (w a).val := by
    intro j
    rcases (hQ j).2 with hEmpty | ⟨i,hi⟩
    · refine ⟨⟨fun _ => 1,FullGammaFunction.one _⟩,?_⟩
      intro a ha
      exact False.elim ((Set.eq_empty_iff_forall_notMem.mp hEmpty) a.val ha)
    · refine ⟨f i,?_⟩
      intro a ha
      obtain ⟨b,hb,hw⟩ := hi ha
      have hba : b = a := Subtype.ext hb
      subst b
      exact hw.symm
  choose F hF using hchoice
  exact ⟨J,Q,F,fun j => (hQ j).1,hdis,hcov,hF⟩
end DiamondIntegral.Section3
