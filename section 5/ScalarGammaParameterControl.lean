import «section 5».ScalarGammaGraphPieces
import «section 3».GammaGroundMapTuples
import «section 3».RVUnitGammaMaps
import Section4.MapProduct

/-! Actual scalar Gamma functions on arbitrary nonzero RV domains become
value functions after a finite partition over the original ground. -/
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

def unitGraphInputValueMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (n : ℕ) :
    Map (DefSet.univ (rawRVUnitSpace (M := M) (n+1)) S)
      (DefSet.univ ((rawRVUnitSpace n).prod (volumeGammaSpace hc)) S) :=
  ((unitTupleInitMap S n).pair
    ((universalPowerCoordinate (volumeGammaSpace hc) S (Fin.last n)).comp
      (rvUnitGammaMap hc S (n+1)))).toUniv

def groundGammaFunctionGraphLift
    {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+1)) where
  carrier := {u | ∃ x : X, x.val = Fin.init u ∧ (f x).val = rvUnitValueHom (u (Fin.last n))}
  definable := f.graph_definable.preimage (unitGraphInputValueMap hc B.real n)

theorem groundGammaFunctionGraphLift_functional
    {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    ScalarGammaGraph (groundGammaFunctionGraphLift f).carrier := by
  rintro u ⟨x, hx, hfx⟩ v ⟨y, hy, hfy⟩ huv
  have hxy : x = y := Subtype.ext (hx.trans ((funext huv).trans hy.symm))
  exact hfx.symm.trans ((congrArg (fun z : X => (f z).val) hxy).trans hfy)

theorem groundGammaFunctionGraphLift_domain
    {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    Fin.init '' (groundGammaFunctionGraphLift f).carrier = X.carrier := by
  ext x
  constructor
  · rintro ⟨u, ⟨y, hy, _⟩, hu⟩
    exact (hy.trans hu) ▸ y.property
  · intro hx
    obtain ⟨t, ht⟩ := rvUnitValueHom_surjective (f ⟨x, hx⟩).val
    refine ⟨Fin.snoc x t, ⟨⟨x, hx⟩, ?_, ?_⟩, ?_⟩
    · funext j
      simp only [Fin.init, Fin.snoc_castSucc]
    · simpa only [Fin.snoc_last] using ht.symm
    · funext j
      simp only [Fin.init, Fin.snoc_castSucc]

theorem groundGammaFunctionGraphLift_row
    {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (x : X) (γ : Values.Gamma (M := M)) :
    unitGammaGraphRow (groundGammaFunctionGraphLift f).carrier x.val γ ↔ (f x).val = γ := by
  constructor
  · rintro ⟨t, ⟨y, hy, hfy⟩, ht⟩
    have hyx : y = x := by
      apply Subtype.ext
      funext j
      simpa only [Fin.init, Fin.snoc_castSucc] using congrFun hy j
    rw [hyx] at hfy
    have he : (f x).val = rvUnitValueHom t := by simpa only [Fin.snoc_last] using hfy
    exact he.trans ht
  · intro hγ
    obtain ⟨t, ht⟩ := rvUnitValueHom_surjective γ
    refine ⟨t, ⟨x, (by funext j; simp only [Fin.init, Fin.snoc_castSucc]), ?_⟩, ht⟩
    simpa only [Fin.snoc_last] using hγ.trans ht.symm

theorem scalar_gamma_parameter_control {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    ∃ N : ℕ, ∃ A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n),
      ∃ D : Fin N → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))),
      (∀ i, (A i).carrier ⊆ X.carrier) ∧
      (∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier) ∧
      (∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (A i).carrier) ∧
      (∀ i α, α ∈ (D i).carrier → ∀ β ∈ (D i).carrier,
        Fin.init α = Fin.init β → α (Fin.last n) = β (Fin.last n)) ∧
      (∀ i (x : X), x.val ∈ (A i).carrier → ∀ γ,
        (f x).val = γ ↔ Fin.snoc (rvUnitTupleValues x.val) γ ∈ (D i).carrier) := by
  obtain ⟨N, P, hd, hcov⟩ := scalar_gamma_graph_value_partition hκ hs h00 hr hγ hΓ
    (groundGammaFunctionGraphLift f) (groundGammaFunctionGraphLift_functional f)
  have hX := groundGammaFunctionGraphLift_domain f
  refine ⟨N, (fun i => (P i).source), (fun i => (P i).graph), ?_, hd, ?_, ?_, ?_⟩
  · intro i x hx
    exact hX ▸ (hcov x).mpr ⟨i, hx⟩
  · intro x
    rw [← hX]
    exact hcov x
  · intro i α hα β hβ hi
    exact (P i).graph_functional α hα β hβ hi
  · intro i x hx γ
    exact (groundGammaFunctionGraphLift_row f x γ).symm.trans ((P i).row x.val hx γ)

end DiamondIntegral.Section5
