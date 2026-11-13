import «section 3».GammaGroundRVFiniteMapRank
import «section 3».GammaGroundMapRealization
import Section4.MixedRVAlgebraicity
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n r m s : ℕ}
variable {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
variable {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)}

theorem gammaGroundMap_output_vf_coordinate_isAlgebraic
    (f : GammaGroundMap A B) (a : A) (j : Fin m)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hS : Cardinal.mk ground.real < κ) :
    IsAlgebraic (tupleField (vfParameterField ground.real) a.val.1) ((f a).val.1 j) := by
  obtain ⟨T, _, _, hfield, hDA, hDB, hgraph⟩ := f.realize hκ hS
  let DA : DefSet (rawMixedSpace (M := M) n r) T := ⟨A.carrier, hDA⟩
  let DB : DefSet (rawMixedSpace (M := M) m s) T := ⟨B.carrier, hDB⟩
  let F : Map DA DB := ⟨f.toFun, (relationDefinable_iff_product _).mpr hgraph⟩
  have h := map_output_vf_coordinate_isAlgebraic hc F a j
  change IsAlgebraic (tupleField (vfParameterField T) a.val.1) ((f a).val.1 j) at h
  rw [hfield] at h
  exact h

theorem gammaGroundMixedMap_output_rv_coordinate_algebraic
    (f : GammaGroundMap A B) (a : A) (j : Fin s)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hγ : GammaRVAlgebraicityInput (M := M) κ)
    (hS : Cardinal.mk ground.real < κ) :
    AlgebraicAt ((ground.real ∪ Set.range (vfValues a.val.1)) ∪ Set.range (rvValues a.val.2))
      .rv ((f a).val.2 j).val := by
  let g : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) s)) :=
    (GammaGroundMap.ofGlobal B _ (rvTailMap (DefSet.univ (rawMixedSpace m s) ground.real))
      (fun _ => Set.mem_univ _)).comp f
  let c : (rawMixedSpace (M := M) n r).domain := ⟨mixedValues a.val, mixedValues_mem_domain a.val⟩
  let E : GammaGroundDefSet hc ⟨ground.real ∪ Set.range c.val, ground.gamma⟩ (rawRVSpace (M := M) s) :=
    ⟨{y | ∃ x : A, x.val = a.val ∧ (g x).val = y}, by
      have hd := (g.graph_definable.preimage
        (universalProductSwap (rawRVSpace s) (rawMixedSpace n r) ground.real)).fibreRealPoint c
      change GammaGroundDefinable hc ⟨ground.real ∪ Set.range c.val, ground.gamma⟩ (rawRVSpace s)
        {y | ∃ x : A, x.val = (rawMixedSpace n r).decode c ∧ (g x).val = y} at hd
      have hca : (rawMixedSpace n r).decode c = a.val := decode_mixedValues a.val
      rw [hca] at hd
      exact hd⟩
  have hE : E.carrier.Finite := Set.Subsingleton.finite (by
    rintro y ⟨x, hx, hxy⟩ z ⟨w, hw, hwz⟩
    have he : x = w := Subtype.ext (hx.trans hw.symm)
    subst w
    exact hxy.symm.trans hwz)
  have ha : GammaParameters.AlgebraicAtBase
      ⟨ground.real ∪ Set.range c.val, ground.gamma⟩ .rv ((f a).val.2 j).val :=
    ⟨gammaGroundRVCoordinateSet E j, gammaGroundRVCoordinateSet_definable E j,
      gammaGroundRVCoordinateSet_finite E hE j, ⟨⟨(g a).val, ⟨a, rfl, rfl⟩⟩, rfl⟩⟩
  have h := (hγ _ (realCodeParameters_small c hκ hS) _).mp ha
  have he : Set.range c.val = Set.range (vfValues a.val.1) ∪ Set.range (rvValues a.val.2) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact Or.inl (Set.mem_range_self i)
      | inr i => exact Or.inr (Set.mem_range_self i)
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨.inl i, rfl⟩
      · exact ⟨.inr i, rfl⟩
  rwa [he, ← Set.union_assoc] at h


theorem gammaGroundMixedMap_vf_base_algebraic
    (f : GammaGroundMap A B) (a : A)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hS : Cardinal.mk ground.real < κ) :
    ground.real ∪ Set.range (vfValues (f a).val.1) ⊆
      algebraicClosureSet (ground.real ∪ Set.range (vfValues a.val.1)) := by
  rintro x (hx | ⟨j, rfl⟩)
  · exact subset_algebraicClosureSet _ (Or.inl hx)
  · refine ⟨.vf, (algebraicAt_vf_iff_parameterField _ _).mpr ?_⟩
    rw [vfParameterField_union_tuple]
    exact gammaGroundMap_output_vf_coordinate_isAlgebraic f a j hκ hS

theorem gammaGroundMixedBijection_point_rv_rank
    (hex : RVExchangeInput (M := M))
    (f : GammaGroundMap A B) (hf : Function.Bijective f) (a : A)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hγ : GammaRVAlgebraicityInput (M := M) κ)
    (hS : Cardinal.mk ground.real < κ) :
    rvTupleRank hc hex (ground.real ∪ Set.range (vfValues (f a).val.1)) (f a).val.2 =
      rvTupleRank hc hex (ground.real ∪ Set.range (vfValues a.val.1)) a.val.2 := by
  have hforward := gammaGroundMixedMap_vf_base_algebraic f a hκ hS
  have hbackward := gammaGroundMixedMap_vf_base_algebraic (f.inverse hf) (f a) hκ hS
  rw [GammaGroundMap.inverse_apply] at hbackward
  have hbase {d : ℕ} (t : Fin d → CanonicalRV.RVSort M) :=
    rvTupleRank_eq_of_mutually_algebraic hc hex hforward hbackward t
  apply Nat.le_antisymm
  · rw [hbase]
    exact rvTupleRank_le_of_algebraic hc hex _ a.val.2 (f a).val.2
      (gammaGroundMixedMap_output_rv_coordinate_algebraic f a · hκ hγ hS)
  · rw [← hbase]
    have h := rvTupleRank_le_of_algebraic hc hex _ (f a).val.2 ((f.inverse hf) (f a)).val.2
      (gammaGroundMixedMap_output_rv_coordinate_algebraic (f.inverse hf) (f a) · hκ hγ hS)
    simpa only [GammaGroundMap.inverse_apply] using h

end DiamondIntegral.Section3
