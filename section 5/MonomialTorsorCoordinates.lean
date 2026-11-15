import «section 5».MonomialCoordinateBijections
import «section 5».UnitTupleLastProducts
import «section 5».MonomialGammaGraphSupports
import «section 3».GammaGroundRVProductLaws

/-! A varying scalar value torsor on a monomial chart is an actual
original-ground product with its reconstructed Gamma support. -/
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

def GroundMonomialPiece.torsorCoordinateBijection (P : GroundMonomialPiece X) :
    GammaGroundBijection
      (P.source.prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) 1)))
      (P.residue.prod (unitTupleLastCylinder (gammaGroundRVUnitGammaPreimage P.gamma))) :=
  ((GammaGroundBijection.id P.residue).prodMap
    (gammaGroundRVUnitTupleProductBijection ((gammaGroundRVUnitGammaPreimage P.gamma).prod
      (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) 1))))).comp
    ((GammaGroundBijection.prodAssoc P.residue (gammaGroundRVUnitGammaPreimage P.gamma)
      (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) 1))).comp
      (P.coordinateBijection.prodMap
        (GammaGroundBijection.id (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) 1)))))

theorem GroundMonomialPiece.torsorCoordinateBijection_value (P : GroundMonomialPiece X)
    (a : P.source.prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) 1))) :
    (P.torsorCoordinateBijection.map a).val =
      ((P.cell.coordinateEquiv P.split a.val.1).1,
        Fin.snoc (α := fun _ : Fin (P.split.freeArity+1) => (CanonicalRV.RVSort M)ˣ)
          (P.cell.coordinateEquiv P.split a.val.1).2 (a.val.2 0)) := by
  change ((P.cell.coordinateEquiv P.split a.val.1).1,
    Fin.append (P.cell.coordinateEquiv P.split a.val.1).2 a.val.2) = _
  have ht : a.val.2 = (fun _ : Fin 1 => a.val.2 0) := by
    funext i
    exact congrArg a.val.2 (Subsingleton.elim i 0)
  rw [ht, finAppendSingleton_eq_snoc]

theorem GroundMonomialPiece.torsorTarget_subset (P : GroundMonomialPiece X)
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1)))) :
    (P.residue.prod (gammaGroundRVUnitGammaPreimage (P.reconstructedGammaGraph D))).carrier ⊆
      (P.residue.prod (unitTupleLastCylinder (gammaGroundRVUnitGammaPreimage P.gamma))).carrier := by
  intro p hp
  refine ⟨hp.1, (unitTupleLastCylinder_mem _ p.2).mpr ?_⟩
  have hK : rvUnitTupleValues p.2 ∈ (P.reconstructedGammaGraph D).carrier := hp.2
  change (rvUnitTupleValues p.2 ∘ Fin.castSucc) ∈ P.gamma.carrier ∧ _ at hK
  change (rvUnitTupleValues p.2 ∘ Fin.castSucc) ∈ P.gamma.carrier
  exact hK.1

def GroundMonomialPiece.reconstructedTorsorSource (P : GroundMonomialPiece X)
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1)))) :=
  P.torsorCoordinateBijection.inverseImage
    (P.residue.prod (gammaGroundRVUnitGammaPreimage (P.reconstructedGammaGraph D)))

def GroundMonomialPiece.reconstructedTorsorBijection (P : GroundMonomialPiece X)
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1)))) :
    GammaGroundBijection (P.reconstructedTorsorSource D)
      (P.residue.prod (gammaGroundRVUnitGammaPreimage (P.reconstructedGammaGraph D))) :=
  P.torsorCoordinateBijection.restrictTarget _ (P.torsorTarget_subset D)

theorem GroundMonomialPiece.reconstructedTorsorSource_mem (P : GroundMonomialPiece X)
    (D : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (p : (Fin n → (CanonicalRV.RVSort M)ˣ) × (Fin 1 → (CanonicalRV.RVSort M)ˣ)) :
    p ∈ (P.reconstructedTorsorSource D).carrier ↔
      p.1 ∈ P.source.carrier ∧ Fin.snoc (rvUnitTupleValues p.1) (rvUnitValueHom (p.2 0)) ∈ D.carrier := by
  constructor
  · rintro ⟨a, ha, hz⟩
    subst p
    rw [P.torsorCoordinateBijection_value a] at hz
    have hK : rvUnitTupleValues (Fin.snoc
        (α := fun _ : Fin (P.split.freeArity+1) => (CanonicalRV.RVSort M)ˣ)
        (P.cell.coordinateEquiv P.split a.val.1).2 (a.val.2 0)) ∈
        (P.reconstructedGammaGraph D).carrier := hz.2
    rw [rvUnitTupleValues_snoc] at hK
    have hD := ((P.reconstructedGammaGraph_row D _ _).mp hK).2
    rw [P.freeValueReconstruction_coordinate a.val.1 a.property.1] at hD
    exact ⟨a.property.1, hD⟩
  · rintro ⟨hx, hD⟩
    let a : P.source.prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) 1)) :=
      ⟨p, hx, Set.mem_univ _⟩
    refine ⟨a, rfl, ?_⟩
    rw [P.torsorCoordinateBijection_value a]
    have hcoord := (P.coordinate_mem_iff p.1).mpr hx
    refine ⟨hcoord.1, ?_⟩
    change rvUnitTupleValues (Fin.snoc
      (α := fun _ : Fin (P.split.freeArity+1) => (CanonicalRV.RVSort M)ˣ)
      (P.cell.coordinateEquiv P.split p.1).2 (p.2 0)) ∈ (P.reconstructedGammaGraph D).carrier
    rw [rvUnitTupleValues_snoc]
    apply (P.reconstructedGammaGraph_row D _ _).mpr
    refine ⟨hcoord.2, ?_⟩
    rw [P.freeValueReconstruction_coordinate p.1 hx]
    exact hD

end DiamondIntegral.Section5
