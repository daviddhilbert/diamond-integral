import «section 6».RVIndexedSpanPaths
import Section9.VolumePairMap

/-! Actual finite-volume RV isomorphisms have interalgebraic source and
target volume tuples. The finite-fibre witnesses come from the actual
volume-pair projection, over the original parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rvHom_volume_coordinate_algebraic (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : RVObject (M := M) S n} (F : RVHom U V) (hU : U.volume.FiniteFibres)
    (u : U.domain) (j : Fin n) :
    AlgebraicAt (S ∪ Set.range (rvValues (U.value u))) .rv (V.value (F.map u) j).val := by
  let P := volumeCorrespondence F.map
  let p : P := volumePairMap F.map u
  let π := rvHeadSelect (productLeft n n) P
  have h := finite_map_rv_coordinate_algebraic hc π
    (volumePair_leftProjection_finite F.map hU) p (productRight n n j)
  have hLeft : (π p).val = U.value u := by
    funext i
    change (volumePairMap F.map u).val (productLeft n n i) = U.value u i
    rw [volumePairMap_apply,productTuple_left]
  have hRight : p.val (productRight n n j) = V.value (F.map u) j := by
    change (volumePairMap F.map u).val (productRight n n j) = _
    rw [volumePairMap_apply,productTuple_right]
  rw [hLeft,hRight] at h
  exact h

theorem rvIso_volume_closure_eq (hc : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) {U V : RVObject (M := M) S n} (e : U ≅ V)
    (hU : U.volume.FiniteFibres) (hV : V.volume.FiniteFibres) (u : U.domain) :
    rvTupleClosure hc hex S (U.value u) = rvTupleClosure hc hex S (V.value (e.hom.map u)) := by
  apply rv_tuple_closure_eq_of_interalgebraic hc hex S
  · exact rvHom_volume_coordinate_algebraic hc e.hom hU u
  · intro j
    have h := rvHom_volume_coordinate_algebraic hc e.inv hV (e.hom.map u) j
    rw [SpecialTransformations.Section4.rvIso_inv_apply] at h
    exact h

theorem rvIso_pointwise_volume_span_path (hc : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) {U V : RVObject (M := M) S n} (e : U ≅ V)
    (hU : U.volume.FiniteFibres) (hV : V.volume.FiniteFibres) (u : U.domain) :
    Relation.ReflTransGen
      (RVIndexedSpanStep hc hex S (productTuple (U.value u) (V.value (e.hom.map u))))
      (productLeft n n) (productRight n n) := by
  apply exists_rvIndexedSpanPath hc hex S
  have hL : productTuple (U.value u) (V.value (e.hom.map u)) ∘ productLeft n n = U.value u :=
    funext (productTuple_left _ _)
  have hR : productTuple (U.value u) (V.value (e.hom.map u)) ∘ productRight n n = V.value (e.hom.map u) :=
    funext (productTuple_right _ _)
  rw [hL,hR]
  exact rvIso_volume_closure_eq hc hex e hU hV u

end DiamondIntegral.Section6
