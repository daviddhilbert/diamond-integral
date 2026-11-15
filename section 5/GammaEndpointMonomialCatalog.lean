import «section 5».FiniteGammaParameterControl
import «section 5».MonomialSourcePartitions

/-! Finite families of actual Gamma functions have finitely many original-ground
monomial source pieces with complete functional value-graph data. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}

structure GammaEndpointMonomialPiece
    {ι : Type} [Fintype ι]
    (f : ι → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) where
  parent : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)
  monomial : GroundMonomialPiece parent
  source_subset : monomial.source.carrier ⊆ X.carrier
  graph : ι → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1)))
  graph_functional : ∀ j α, α ∈ (graph j).carrier → ∀ β ∈ (graph j).carrier,
    Fin.init α = Fin.init β → α (Fin.last n) = β (Fin.last n)
  row : ∀ j (x : monomial.source) γ, (((f j).restrict source_subset) x).val = γ ↔
    Fin.snoc (rvUnitTupleValues x.val) γ ∈ (graph j).carrier

theorem gamma_endpoint_monomial_catalog {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {ι : Type} [Fintype ι]
    (f : ι → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    ∃ N : ℕ, ∃ C : Fin N → GammaEndpointMonomialPiece f,
      (∀ i j, i ≠ j → Disjoint (C i).monomial.source.carrier (C j).monomial.source.carrier) ∧
      ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (C i).monomial.source.carrier := by
  obtain ⟨N, A, D, hsub, hdis, hcov, hfun, hrow⟩ := finite_scalar_gamma_parameter_control hκ hs h00 hr hγ hΓ X f
  choose L P hPd hPc using (fun i => ground_monomial_source_partition hκ hs h00 hr hγ hΓ (A i))
  let J := (i : Fin N) × Fin (L i)
  let C : J → GammaEndpointMonomialPiece f := fun j => {
    parent := A j.1
    monomial := P j.1 j.2
    source_subset := fun x hx => hsub j.1 (((P j.1 j.2).source_cut ▸ hx).1)
    graph := D j.1
    graph_functional := hfun j.1
    row := by
      intro k x γ
      have hxA : x.val ∈ (A j.1).carrier :=
        ((Set.ext_iff.mp (P j.1 j.2).source_cut x.val).mp x.property).1
      exact hrow j.1 k ⟨x.val, hsub j.1 hxA⟩ hxA γ }
  have hd : ∀ i j : J, i ≠ j → Disjoint (C i).monomial.source.carrier (C j).monomial.source.carrier := by
    rintro ⟨i,j⟩ ⟨k,l⟩ hne
    by_cases hik : i = k
    · subst k
      exact hPd i j l (fun he => hne (by cases he; rfl))
    · apply (hdis i k hik).mono
      · intro x hx
        exact ((P i j).source_cut ▸ hx).1
      · intro x hx
        exact ((P k l).source_cut ▸ hx).1
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, fun i => C (e i), fun i j hij => hd _ _ (fun he => hij (e.injective he)), ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := (hcov x).mp hx
    obtain ⟨j, hj⟩ := (hPc i x).mp hi
    obtain ⟨k, hk⟩ := e.surjective ⟨i,j⟩
    refine ⟨k, ?_⟩
    change x ∈ (C (e k)).monomial.source.carrier
    rw [hk]
    exact hj
  · rintro ⟨i, hi⟩
    exact (C (e i)).source_subset hi

end DiamondIntegral.Section5
