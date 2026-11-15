import «section 5».MonomialDecomposition
import «section 5».MonomialScalarValueGraphs
import Mathlib.Data.Fintype.Sigma

/-! Global original-ground monomial charts in unimodular-basis form.
Each coordinate map is an integer monomial basis equivalence followed by
the recorded coordinate split. Empty charts are removed, and the source
pieces are induced by a disjoint partition of the original value image. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
noncomputable section
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}

theorem GroundMonomialPiece.coordinate_mem_iff (P : GroundMonomialPiece X)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    P.cell.coordinateEquiv P.split x ∈ (P.residue.prod (gammaGroundRVUnitGammaPreimage P.gamma)).carrier ↔
      x ∈ P.source.carrier := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := P.coordinate_image.symm ▸ hx
    exact (P.cell.coordinateEquiv P.split).injective he ▸ hy
  · intro hx
    exact P.coordinate_image ▸ ⟨x, hx, rfl⟩

theorem GroundMonomialPiece.active_values (P : GroundMonomialPiece X)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) (hx : x ∈ P.source.carrier) :
    rvUnitTupleValues (P.cell.coordinateEquiv P.split x).1 = P.beta := by
  have h := (P.coordinate_mem_iff x).mpr hx
  have hm : rvUnitTupleValues (P.cell.coordinateEquiv P.split x).1 ∈
      rvUnitTupleValues '' P.residue.carrier := ⟨_, h.1, rfl⟩
  rw [P.residue_values] at hm
  exact hm

theorem GroundMonomialPiece.rectangle_reconstruction (P : GroundMonomialPiece X)
    (x y z : Fin n → (CanonicalRV.RVSort M)ˣ) (hx : x ∈ P.source.carrier) (hy : y ∈ P.source.carrier)
    (hactive : ∀ i, integerMonomialMap (integerBasisMatrix P.cell.basis) z (P.split.zeroIndex i) =
      integerMonomialMap (integerBasisMatrix P.cell.basis) x (P.split.zeroIndex i))
    (hvalues : ∀ j, rvUnitValueHom (z j) = rvUnitValueHom (y j)) : z ∈ P.source.carrier := by
  let e := P.cell.coordinateEquiv P.split
  have hx' := (P.coordinate_mem_iff x).mpr hx
  have hy' := (P.coordinate_mem_iff y).mpr hy
  have hfirst : (e z).1 = (e x).1 := by
    funext i
    exact hactive i
  have hlast : rvUnitTupleValues (e z).2 = rvUnitTupleValues (e y).2 := by
    funext i
    change rvUnitValueHom (integerMonomialMap (integerBasisMatrix P.cell.basis) z (P.split.freeIndex i)) =
      rvUnitValueHom (integerMonomialMap (integerBasisMatrix P.cell.basis) y (P.split.freeIndex i))
    simp only [integerMonomialMap, map_prod, map_zpow]
    apply Finset.prod_congr rfl
    intro j _
    rw [hvalues j]
  apply (P.coordinate_mem_iff z).mp
  constructor
  · change (e z).1 ∈ P.residue.carrier
    rw [hfirst]
    exact hx'.1
  · change rvUnitTupleValues (e z).2 ∈ P.gamma.carrier
    rw [hlast]
    exact hy'.2

theorem GroundMonomialPiece.scalar_graph_value_unique {d : ℕ}
    {Y : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (d+1))}
    (P : GroundMonomialPiece Y)
    (hgraph : ∀ x ∈ Y.carrier, ∀ y ∈ Y.carrier,
      (∀ j : Fin d, x j.castSucc = y j.castSucc) →
        rvUnitValueHom (x (Fin.last d)) = rvUnitValueHom (y (Fin.last d)))
    (x y : Fin (d+1) → (CanonicalRV.RVSort M)ˣ) (hx : x ∈ P.source.carrier) (hy : y ∈ P.source.carrier)
    (hvalues : ∀ j : Fin d, rvUnitValueHom (x j.castSucc) = rvUnitValueHom (y j.castSucc)) :
    rvUnitValueHom (x (Fin.last d)) = rvUnitValueHom (y (Fin.last d)) := by
  apply monomial_scalar_graph_value_unique rvUnitValueHom (integerBasisMatrix P.cell.basis)
    P.split.zeroIndex P.source.carrier ?_ ?_ ?_ x y hx hy hvalues
  · intro u hu v hv i
    exact congrFun ((P.active_values u hu).trans (P.active_values v hv).symm) i
  · intro u hu v hv w ha hf
    exact P.rectangle_reconstruction u v w hu hv ha hf
  · intro u hu v hv he
    have hu' : u ∈ Y.carrier := (P.source_cut ▸ hu).1
    have hv' : v ∈ Y.carrier := (P.source_cut ▸ hv).1
    exact hgraph u hu' v hv' he

end DiamondIntegral.Section5
