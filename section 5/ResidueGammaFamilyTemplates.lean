import «section 3».GammaGroundRVUnitProducts
import «section 5».GroundValueCells

/-! A Gamma family over a finite-value residue domain has finitely many
original-ground templates. The empty-fibre region is retained explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

theorem residue_gamma_family_templates {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod ((volumeGammaSpace hc).power (Fin m))))
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hA : (rvUnitTupleValues '' A.carrier).Finite)
    (hsub : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ A.carrier) :
    ∃ N : ℕ, ∃ R : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n),
      ∃ G : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)),
      (∀ i, (R i).carrier ⊆ A.carrier) ∧
      (∀ i, (rvUnitTupleValues '' (R i).carrier).Finite) ∧
      (∀ i j, i ≠ j → Disjoint (R i).carrier (R j).carrier) ∧
      (∀ x, x ∈ A.carrier ↔ ∃ i, x ∈ (R i).carrier) ∧
      (∀ i x, x ∈ (R i).carrier → ∀ γ, (x,γ) ∈ T.carrier ↔ γ ∈ (G i).carrier) := by
  obtain ⟨N, R, G, _, hd, hcov⟩ :=
    gammaGroundRVUnitMixed_definable_products hκ hs h00 hr hγ hΓ T A hA hsub
  let U : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) :=
    ⟨⋃ i, (R i).carrier, GammaGroundDefinable.iUnion (fun i => (R i).definable)⟩
  let Q : Fin (N+1) → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) :=
    Fin.cases (A.inter U.compl) (fun i => A.inter (R i))
  let H : Fin (N+1) → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)) :=
    Fin.cases (GammaGroundDefSet.empty hc B _) G
  have hQA : ∀ i, (Q i).carrier ⊆ A.carrier := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> exact fun _ h => h.1
  refine ⟨N+1, Q, H, hQA, fun i => hA.subset (Set.image_mono (hQA i)), ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun a => ?_) i
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact (hij rfl).elim
      · intro _
        apply Set.disjoint_left.mpr
        intro x hx hy
        exact hx.2 (Set.mem_iUnion.mpr ⟨b, hy.2⟩)
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro _
        apply Set.disjoint_left.mpr
        intro x hx hy
        exact hy.2 (Set.mem_iUnion.mpr ⟨a, hx.2⟩)
      · intro hij
        apply Set.disjoint_left.mpr
        intro x hx hy
        exact Set.disjoint_left.mp (hd a b (fun hab => hij (congrArg Fin.succ hab))) hx.2 hy.2
  · intro x
    constructor
    · intro hx
      by_cases hu : x ∈ U.carrier
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
        exact ⟨i.succ, hx, hi⟩
      · exact ⟨0, hx, hu⟩
    · rintro ⟨i, hi⟩
      exact hQA i hi
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro x hx γ
      constructor
      · intro ht
        obtain ⟨j, hj, _⟩ := (hcov x γ).mp ht
        exact (hx.2 (Set.mem_iUnion.mpr ⟨j, hj⟩)).elim
      · exact False.elim
    · intro x hx γ
      constructor
      · intro ht
        obtain ⟨k, hk, hγk⟩ := (hcov x γ).mp ht
        have he : k = j := by
          by_contra hne
          exact Set.disjoint_left.mp (hd k j hne) hk hx.2
        exact he ▸ hγk
      · intro hγj
        exact (hcov x γ).mpr ⟨j, hx.2, hγj⟩

end DiamondIntegral.Section5
