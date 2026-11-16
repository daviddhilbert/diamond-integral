import «section 6».PureRVImageGraphs

/-! Actual unary volume-coordinate correspondences of RV morphisms.
Their full original-base graphs, sort conditions and finite forward
fibres meet every hypothesis of the uniform inverse-obstacle theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def rvCoordinateRelation {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1)) :
    Set ((Fin (n+1) → M) × M) :=
  {p | ∃ u : U.domain, rvValues (U.value u) = p.1 ∧ (V.value (F.map u) j).val = p.2}

theorem rvCoordinateRelation_definable {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1)) :
    RawClosure.Tuple.RelationDefinable S (rvCoordinateRelation F j) := by
  let g := (rvTupleSelectMap S (fun _ : Fin 1 => j)).comp (V.volume.comp F.map)
  have h := rvPairMap_code_image_definable U.volume g
  change S.Definable LRV {z : Fin (n+1) ⊕ Fin 1 → M |
    ∃ u : U.domain, rvValues (U.value u) = z ∘ Sum.inl ∧ (V.value (F.map u) j).val = z (.inr 0)}
  convert h using 1
  ext z
  constructor
  · rintro ⟨u,hu,hv⟩
    refine ⟨u,hu,funext (fun i => ?_)⟩
    fin_cases i
    exact hv
  · rintro ⟨u,hu,hv⟩
    exact ⟨u,hu,congrFun hv 0⟩

theorem rvCoordinateRelation_sorted {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1))
    (t : Fin n → M) (x y : M) (h : (Fin.snoc t x,y) ∈ rvCoordinateRelation F j) : iRV x ∧ iRV y := by
  obtain ⟨u,hu,hv⟩ := h
  have hx := congrFun hu (Fin.last n)
  simp only [rvValues,Fin.snoc_last] at hx
  change (V.value (F.map u) j).val = y at hv
  exact ⟨hx ▸ (U.value u (Fin.last n)).property,hv ▸ (V.value (F.map u) j).property⟩

theorem rvCoordinateRelation_forward_finite {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1))
    (t : Fin n → M) (x : M) : {y | (Fin.snoc t x,y) ∈ rvCoordinateRelation F j}.Finite := by
  by_cases ht : ∃ s : Fin (n+1) → RVInfinity M, rvValues s = Fin.snoc t x
  · obtain ⟨s,hs⟩ := ht
    apply ((F.finite_volume_images s).image (fun z => (z j).val)).subset
    rintro y ⟨u,hu,hv⟩
    have hvol : U.value u = s := rvValues_injective (hu.trans hs.symm)
    exact ⟨V.value (F.map u),⟨u,hvol,rfl⟩,hv⟩
  · have he : {y | (Fin.snoc t x,y) ∈ rvCoordinateRelation F j} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨u,hu,_⟩
      exact ht ⟨U.value u,hu⟩
    rw [he]
    exact Set.finite_empty

theorem exists_rv_coordinate_inverse_obstacles
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1)) :
    ∃ E : RawClosure.Tuple.GoodRelation (n := n) S, ∃ N : ℕ,
      ∀ (t : Fin n → M) (y : M), (t,y) ∉ E.val →
        {x | (Fin.snoc t x,y) ∈ rvCoordinateRelation F j}.Finite ∧
          {x | (Fin.snoc t x,y) ∈ rvCoordinateRelation F j}.ncard ≤ N :=
  exists_uniform_rv_inverse_obstacles hc h00 hκ hs hsmall (rvCoordinateRelation F j)
    (rvCoordinateRelation_definable F j) (rvCoordinateRelation_sorted F j)
    (rvCoordinateRelation_forward_finite F j)

end DiamondIntegral.Section6
