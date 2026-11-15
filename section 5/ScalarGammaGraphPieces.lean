import «section 5».MonomialPieceScalarGraphs
import «section 5».UnitTupleProjection

/-! Scalar Gamma-valued graphs have a finite original-ground partition
of their RV input domain on which the graph depends only on input values. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def ScalarGammaGraph (Y : Set (Fin (n+1) → (CanonicalRV.RVSort M)ˣ)) : Prop :=
  ∀ x ∈ Y, ∀ y ∈ Y, (∀ j : Fin n, x j.castSucc = y j.castSucc) →
    rvUnitValueHom (x (Fin.last n)) = rvUnitValueHom (y (Fin.last n))

def unitGammaGraphRow (Y : Set (Fin (n+1) → (CanonicalRV.RVSort M)ˣ))
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) (γ : Values.Gamma (M := M)) : Prop :=
  ∃ t, Fin.snoc x t ∈ Y ∧ rvUnitValueHom t = γ

theorem GroundMonomialPiece.scalar_value_image_functional
    {Y : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+1))}
    (P : GroundMonomialPiece Y) (hgraph : ScalarGammaGraph Y.carrier)
    (α β : Fin (n+1) → Values.Gamma (M := M))
    (hα : α ∈ (groundRVValueImage P.source).carrier)
    (hβ : β ∈ (groundRVValueImage P.source).carrier) (hi : Fin.init α = Fin.init β) :
    α (Fin.last n) = β (Fin.last n) := by
  rw [groundRVValueImage_carrier] at hα hβ
  obtain ⟨x, hx, rfl⟩ := hα
  obtain ⟨y, hy, rfl⟩ := hβ
  exact P.scalar_graph_value_unique hgraph x y hx hy (fun j => congrFun hi j)

theorem GroundMonomialPiece.scalar_value_image_row
    {Y : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+1))}
    (P : GroundMonomialPiece Y) (hgraph : ScalarGammaGraph Y.carrier)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hx : x ∈ (groundUnitTupleInitMap P.source).image.carrier) (γ : Values.Gamma (M := M)) :
    unitGammaGraphRow Y.carrier x γ ↔
      Fin.snoc (rvUnitTupleValues x) γ ∈ (groundRVValueImage P.source).carrier := by
  rw [groundUnitTupleInitMap_image] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  have huY : u ∈ Y.carrier := (P.source_cut ▸ hu).1
  constructor
  · rintro ⟨t, ht, hγ⟩
    have he := hgraph u huY (Fin.snoc (Fin.init u) t) ht (by
      intro j
      simp only [Fin.snoc_castSucc, Fin.init])
    have heγ : rvUnitValueHom (u (Fin.last n)) = γ := by
      have he' : rvUnitValueHom (u (Fin.last n)) = rvUnitValueHom t := by
        simpa only [Fin.snoc_last] using he
      exact he'.trans hγ
    rw [groundRVValueImage_carrier]
    refine ⟨u, hu, ?_⟩
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [Fin.snoc_last, rvUnitTupleValues] using heγ
    · simp only [Fin.snoc_castSucc, rvUnitTupleValues, Fin.init]
  · intro hγ
    rw [groundRVValueImage_carrier] at hγ
    obtain ⟨w, hw, he⟩ := hγ
    have huvalue : rvUnitValueHom (u (Fin.last n)) = rvUnitValueHom (w (Fin.last n)) := by
      apply P.scalar_graph_value_unique hgraph u w hu hw
      intro j
      have hh := congrFun he j.castSucc
      simpa only [Fin.snoc_castSucc, rvUnitTupleValues, Fin.init] using hh.symm
    have hwvalue : rvUnitValueHom (w (Fin.last n)) = γ := by
      have hh := congrFun he (Fin.last n)
      simpa only [Fin.snoc_last, rvUnitTupleValues] using hh
    refine ⟨u (Fin.last n), ?_, huvalue.trans hwvalue⟩
    simpa only [Fin.snoc_init_self] using huY

structure ScalarGammaGraphPiece
    (Y : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+1))) where
  source : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)
  graph : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1)))
  graph_functional : ∀ α ∈ graph.carrier, ∀ β ∈ graph.carrier,
    Fin.init α = Fin.init β → α (Fin.last n) = β (Fin.last n)
  row : ∀ x ∈ source.carrier, ∀ γ, unitGammaGraphRow Y.carrier x γ ↔
    Fin.snoc (rvUnitTupleValues x) γ ∈ graph.carrier

def scalarGammaGraphPieceOfMonomial
    {Y : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+1))}
    (P : GroundMonomialPiece Y) (hgraph : ScalarGammaGraph Y.carrier) : ScalarGammaGraphPiece Y where
  source := (groundUnitTupleInitMap P.source).image
  graph := groundRVValueImage P.source
  graph_functional := fun α hα β hβ hi => P.scalar_value_image_functional hgraph α β hα hβ hi
  row := fun x hx γ => P.scalar_value_image_row hgraph x hx γ

theorem scalar_gamma_graph_value_partition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (Y : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+1))) (hgraph : ScalarGammaGraph Y.carrier) :
    ∃ N : ℕ, ∃ P : Fin N → ScalarGammaGraphPiece Y,
      (∀ i j, i ≠ j → Disjoint (P i).source.carrier (P j).source.carrier) ∧
      ∀ x, x ∈ Fin.init '' Y.carrier ↔ ∃ i, x ∈ (P i).source.carrier := by
  obtain ⟨N, C, hd, hcov⟩ := ground_global_monomial_decomposition hκ hs h00 hr hγ hΓ Y
  let P := fun i => scalarGammaGraphPieceOfMonomial (C i) hgraph
  refine ⟨N, P, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro t hi hj
    rw [show (P i).source.carrier = Fin.init '' (C i).source.carrier from groundUnitTupleInitMap_image _] at hi
    rw [show (P j).source.carrier = Fin.init '' (C j).source.carrier from groundUnitTupleInitMap_image _] at hj
    obtain ⟨u, hu, hut⟩ := hi
    obtain ⟨v, hv, hvt⟩ := hj
    have hu' := (C i).source_cut ▸ hu
    have hv' := (C j).source_cut ▸ hv
    have hlast := hgraph u hu'.1 v hv'.1 (fun k => congrFun (hut.trans hvt.symm) k)
    have hvalues : rvUnitTupleValues u = rvUnitTupleValues v := by
      funext k
      refine Fin.lastCases hlast (fun k => ?_) k
      exact congrArg rvUnitValueHom (congrFun (hut.trans hvt.symm) k)
    exact Set.disjoint_left.mp (hd i j hij) hu'.2 (hvalues.symm ▸ hv'.2)
  · intro x
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, hi⟩ := (hcov (rvUnitTupleValues u)).mp ⟨u, hu, rfl⟩
      refine ⟨i, ?_⟩
      change Fin.init u ∈ (groundUnitTupleInitMap (C i).source).image.carrier
      rw [groundUnitTupleInitMap_image]
      exact ⟨u, (C i).source_cut.symm ▸ ⟨hu, hi⟩, rfl⟩
    · rintro ⟨i, hi⟩
      change x ∈ (groundUnitTupleInitMap (C i).source).image.carrier at hi
      rw [groundUnitTupleInitMap_image] at hi
      obtain ⟨u, hu, he⟩ := hi
      exact ⟨u, ((C i).source_cut ▸ hu).1, he⟩

end DiamondIntegral.Section5
