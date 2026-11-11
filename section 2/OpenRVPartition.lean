import «section 2».RawRVPolydiscs

/-! The RV-row partition consequence of Corollary 2.30, stated directly
for finite-valued VF correspondences with their exact original domains. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem finitary_open_rv_partition
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (image : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    (D : Set (Fin n → M)) (hD : DefinableOver S (fun _ => .vf) D)
    (F : (Fin n → M) → Set M)
    (hF : DefinableOver S (fun _ : Fin (n+1) => .vf)
      {z | Fin.init z ∈ D ∧ z (Fin.last n) ∈ F (Fin.init z)})
    (hfinite : ∀ x ∈ D, (F x).Finite) (hrv : ∀ x ∈ D, Set.InjOn iRv (F x)) :
    ∃ Q : Set (Set (Fin n → M)), Q.Finite ∧ Q.PairwiseDisjoint id ∧
      (∀ V ∈ Q, V.Nonempty ∧ V ⊆ D ∧ DefinableOver S (fun _ => .vf) V ∧ OpenRVRowsConstant F V) ∧
      ∀ x ∈ D, ∃ V ∈ Q, x ∈ V := by
  let G : Set ((Fin n → M) × M) := {p | p.1 ∈ D ∧ p.2 ∈ F p.1}
  have hG : DefinableOver S (fun _ : Fin (n+1) => .vf) {z | (Fin.init z,z (Fin.last n)) ∈ G} := hF
  have hrows (x : Fin n → M) (hx : x ∈ D) : {y | (x,y) ∈ G} = F x :=
    Set.ext (fun y => and_iff_right hx)
  have hGfin : ∀ x ∈ D, {y | (x,y) ∈ G}.Finite := by
    intro x hx
    rw [hrows x hx]
    exact hfinite x hx
  have hGinj : ∀ x ∈ D, Set.InjOn iRv {y | (x,y) ∈ G} := by
    intro x hx
    rw [hrows x hx]
    exact hrv x hx
  obtain ⟨Q,hQf,hQdis,hQ,hcov⟩ := corollary_2_30 hc h00 hs S hsmall hΓ unary rvbase image D hD G hG hGfin hGinj
  refine ⟨Q,hQf,hQdis,?_,hcov⟩
  intro V hV
  obtain ⟨hne,hVD,hVdef,hbranch⟩ := hQ V hV
  refine ⟨hne,hVD,hVdef,?_⟩
  intro a δ hpoly x hx y hy
  have hconst := TaggedPolydiscBranchDecomposition.rows_constant ⟨S,∅⟩ a δ G
    (hbranch a δ hpoly) x hx y hy
  rwa [hrows x (hVD (hpoly hx)),hrows y (hVD (hpoly hy))] at hconst

end DiamondIntegral.Section2
