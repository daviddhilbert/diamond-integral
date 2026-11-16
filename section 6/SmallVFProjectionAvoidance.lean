import «section 6».MixedVFProjectionMaps
import Section4.CoordinateMaps
import Section4.RVWeightDimension

/-! The VF projection of an actual VF-small set misses a point in
every nonzero RV polydisc. Erasing all RV labels first preserves the
dimension bound, so this assertion concerns the entire projection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem vfSmall_projection_misses_rv_polydisc
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (E : DefSet (rawMixedSpace (M := M) n r) S)
    (hDim : vfDim (rawRVSpace (M := M) 1) E < n)
    (t : Fin n → RVInfinity M) (ht : ∀ i, (t i).val ≠ iRVZero) :
    ∃ x : Fin n → VF M, tupleRV M x = t ∧ x ∉ (mixedVFHeadMap E).image.carrier := by
  let A := (mixedVFHeadMap E).image
  let Q := (mixedEraseRVMap E).image
  have hQ : vfDim (rawRVSpace (M := M) 1) Q < n :=
    lt_of_le_of_lt (vfDim_image_le hc hs hsmall (rawRVSpace (M := M) 1)
      (rawRVSpace_rvCoded 1) (mixedEraseRVMap E)) hDim
  obtain ⟨a,ha⟩ := DiamondIntegral.Section2.tupleRV_surjective t
  have ha0 (i : Fin n) : a i ≠ 0 := by
    intro h0
    apply ht i
    have he := congrArg Subtype.val (congrFun ha i)
    change (CanonicalRV.encodedRv (a i)).val = (t i).val at he
    exact he.symm.trans ((CanonicalRV.encodedRv_zero_iff (a i)).mpr h0)
  let D : ValuedPolydisc (Valued.v : Valuation (VF M) G) n := ⟨a,a,ha0⟩
  have hRV (x : Fin n → VF M) (hx : x ∈ D.carrier) : tupleRV M x = t := by
    have he : tupleRV M x = tupleRV M a := by
      funext i
      apply Subtype.ext
      apply (CanonicalRV.encoded_eq_iff_close (x i).property (a i).property
        (fun h => ha0 i (Subtype.ext h))).mpr
      change ¬ VFValued.predV (a i) (x i-a i)
      rw [hv,not_le]
      exact hx i
    exact he.trans ha
  by_contra hNo
  have hAll (x : Fin n → VF M) (hx : tupleRV M x = t) : x ∈ A.carrier := by
    by_contra hxA
    exact hNo ⟨x,hx,hxA⟩
  have hBox (x : Fin n → VF M) (hx : x ∈ D.carrier) : (x,Fin.elim0) ∈ Q.carrier := by
    obtain ⟨u,hu⟩ := hAll x (hRV x hx)
    change u.val.1 = x at hu
    exact ⟨u,Prod.ext hu rfl⟩
  have hFull := vfDim_eq_arity_of_contains_polydisc hc hs hsmall (rawRVSpace (M := M) 1)
    (rawRVSpace_rvCoded 1) hv Q Fin.elim0 D hBox
  rw [hFull] at hQ
  exact (lt_irrefl n) hQ

end DiamondIntegral.Section6
