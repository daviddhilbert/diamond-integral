import «section 3».RVAngularResidueUniqueness
import «section 3».GammaGroundRVUnitSingletons
import «section 3».GammaGroundRVFiniteValueFibres
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- Residue points in a square unimodular graph chart are individually
definable over the original ground, after their finite value support is split. -/
theorem gammaGroundRVAngularProduct_residue_singleton_piece
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) (I : Fin K.freeArity → Fin n)
    (hunit : IsUnit (Matrix.submatrix (E.inverseFreeMatrix K) I id).det)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) K.zeroArity))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin K.freeArity))) (hG : G.carrier.Nonempty)
    (hrect : ∀ r ∈ R.carrier, ∀ u, rvUnitTupleValues u ∈ G.carrier →
      (E.coordinateEquiv K).symm (r,u) ∈ X.carrier)
    (hinj : Set.InjOn (fun z => z ∘ I) X.carrier) (r : R) :
    ∃ Q : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) K.zeroArity),
      Q.carrier ⊆ R.carrier ∧ r.val ∈ Q.carrier ∧ Subsingleton Q := by
  obtain ⟨N,δ,Q,_,hQ,_,hcov⟩ := gammaGroundRVUnit_finite_value_fibres R hR
  obtain ⟨j,hj⟩ := (hcov r.val).mp r.property
  have hsub : (Q j).carrier ⊆ R.carrier := fun s hs => (hQ j ▸ hs).1
  have hval : ∀ a ∈ (Q j).carrier, ∀ b ∈ (Q j).carrier,
      rvUnitTupleValues a = rvUnitTupleValues b := by
    intro a ha b hb
    exact (hQ j ▸ ha).2.trans (hQ j ▸ hb).2.symm
  letI : Subsingleton (Q j) := rvAngularProduct_residue_subsingleton E K I hunit (Q j).carrier G.carrier hG hval
    (fun s hs u hu => hrect s (hsub hs) u hu) hinj
  exact ⟨Q j,hsub,hj,inferInstance⟩

theorem gammaGroundRVAngularProduct_residue_point_definable
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) (I : Fin K.freeArity → Fin n)
    (hunit : IsUnit (Matrix.submatrix (E.inverseFreeMatrix K) I id).det)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) K.zeroArity))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin K.freeArity))) (hG : G.carrier.Nonempty)
    (hrect : ∀ r ∈ R.carrier, ∀ u, rvUnitTupleValues u ∈ G.carrier →
      (E.coordinateEquiv K).symm (r,u) ∈ X.carrier)
    (hinj : Set.InjOn (fun z => z ∘ I) X.carrier) (r : R) :
    ∀ i, DefinableClosureAtBase B .rv (rvUnitValues r.val i) := by
  obtain ⟨Q,hsub,hr,hQ⟩ := gammaGroundRVAngularProduct_residue_singleton_piece X E K I hunit R hR G hG hrect hinj r
  letI : Subsingleton Q := hQ
  exact gammaGroundRVUnit_subsingleton_point_definable Q ⟨r.val,hr⟩
end DiamondIntegral.Section3
