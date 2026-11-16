import «section 6».SmallVFProjectionAvoidance
import Section9.LiftLabelRepresentatives

/-! A VF-small exceptional set in a nonzero finite-volume lift meets
only an RV-small set of old labels. Whole bad polydiscs can therefore
be replaced in induction on RV dimension. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def badRVLiftLabels (U : RVObject (M := M) S n)
    (E : DefSet (rawMixedSpace (M := M) n U.arity) S) (hE : E.carrier ⊆ (rvLift U).carrier) :=
  ((liftLabelMap U).restrict hE).image

theorem badRVLiftLabels_subset (U : RVObject (M := M) S n)
    (E : DefSet (rawMixedSpace (M := M) n U.arity) S) (hE : E.carrier ⊆ (rvLift U).carrier) :
    (badRVLiftLabels U E hE).carrier ⊆ U.domain.carrier := by
  rintro u ⟨p,hp⟩
  exact hp ▸ (liftLabelMap U ⟨p.val,hE p.property⟩).property

theorem badRVLiftLabels_volume_in_boundary
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : RVObject (M := M) S n) (hU : ∀ u k, (U.value u k).val ≠ iRVZero)
    (E : DefSet (rawMixedSpace (M := M) n U.arity) S) (hE : E.carrier ⊆ (rvLift U).carrier)
    (hDim : vfDim (rawRVSpace (M := M) 1) E < n) (u : badRVLiftLabels U E hE) :
    U.value ⟨u.val,badRVLiftLabels_subset U E hE u.property⟩ ∈
      (vfRVBoundary hc (mixedVFHeadMap E).image).carrier := by
  let v : U.domain := ⟨u.val,badRVLiftLabels_subset U E hE u.property⟩
  obtain ⟨p,hp⟩ := u.property
  change p.val.2 = u.val at hp
  obtain ⟨w,hw,hVol⟩ := hE p.property
  have hwv : w = v := Subtype.ext (hw.trans hp)
  have hRV : tupleRV M p.val.1 = U.value v := by
    rw [← hwv]
    exact hVol.symm
  obtain ⟨x,hx,hxA⟩ := vfSmall_projection_misses_rv_polydisc hc hs hsmall hv E hDim (U.value v) (hU v)
  exact ⟨⟨p.val.1,⟨p,rfl⟩,hRV⟩,⟨x,hxA,hx⟩⟩

theorem badRVLiftLabels_dimension_drop
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : RVObject (M := M) S (n+1)) (hUF : U.volume.FiniteFibres)
    (hU : ∀ u k, (U.value u k).val ≠ iRVZero)
    (E : DefSet (rawMixedSpace (M := M) (n+1) U.arity) S) (hE : E.carrier ⊆ (rvLift U).carrier)
    (hDim : vfDim (rawRVSpace (M := M) 1) E < n+1) : rvDim (badRVLiftLabels U E hE) < n+1 := by
  let D := badRVLiftLabels U E hE
  let hD := badRVLiftLabels_subset U E hE
  let B := vfRVBoundary hc (mixedVFHeadMap E).image
  let f : Map D B := (U.volume.restrict hD).corestrict
    (badRVLiftLabels_volume_in_boundary hc hs hsmall hv U hU E hE hDim)
  have hf : f.FiniteFibres := by
    intro b
    apply ((hUF.restrict hD) (⟨b.val,Set.mem_univ _⟩ : DefSet.univ (rawRVSpace (M := M) (n+1)) S)).subset
    intro u hu
    exact Subtype.ext (congrArg (fun x : B => x.val) hu)
  obtain ⟨g,hg⟩ := exists_vfRVBoundary_finite_map hc h00 hκ hs hsmall hΓ (mixedVFHeadMap E).image
  exact Nat.lt_succ_of_le ((rvDim_le_iff D n).mpr ⟨n,le_rfl,g.comp f,hg.comp hf⟩)

end DiamondIntegral.Section6
