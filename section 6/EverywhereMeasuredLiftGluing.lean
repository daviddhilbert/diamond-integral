import «section 6».EverywhereMeasuredLiftRestrictions

/-! Finite gluing of actual everywhere measured lifts along disjoint
whole-label pieces, with full total derivatives retained everywhere. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem exists_glued_everywhere_measured_lift {I : Type} [Finite I]
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (P : I → DefSet (rawRVSpace (M := M) U.object.arity) S)
    (hP : ∀ i,(P i).carrier ⊆ U.object.domain.carrier)
    (hCover : ∀ u : U.object.domain,∃ i,u.val ∈ (P i).carrier)
    (hDisj : ∀ i j z,z ∈ (P i).carrier → z ∈ (P j).carrier → i=j)
    (F : ∀ i,EverywhereMeasuredRVLift (e.restrict (P i) (hP i))) :
    Nonempty (EverywhereMeasuredRVLift e) := by
  have hLabel (i) (p : rvLift (U.object.restrict (P i) (hP i))) :
      e.iso.hom.map.graph p.val.2 ((F i).map p).val.2 := by
    obtain ⟨u,hu,hv⟩ := (F i).labels p
    exact ⟨⟨u.val,hP i u.property⟩,hu,hv⟩
  obtain ⟨g,hg,hgLabel,hAgree⟩ := exists_glued_label_lift e.iso P hP hCover hDisj
    (fun i => (F i).map) (fun i => (F i).bijective) hLabel
  refine ⟨⟨g,hg,hgLabel,fun p => ?_⟩⟩
  obtain ⟨i,hi⟩ := hCover (liftLabelMap U.object p)
  let q : rvLift (U.object.restrict (P i) (hP i)) :=
    ⟨p.val,(rvLift_restrict_mem_iff U.object (P i) (hP i) _).mpr ⟨p.property,hi⟩⟩
  obtain ⟨L,hL,hJ⟩ := (F i).measure q
  refine ⟨L,mixedDerivative_of_label_restriction (U := U.object) (V := V.object)
    (P i) (hP i) (F i).map g q p rfl
    (hAgree i) hL,?_⟩
  let W := V.restrict (e.iso.hom.map.restrict (hP i)).image (rvLabelImage_subset e.iso (P i) (hP i))
  let v := liftLabelMap W.object ((F i).map q)
  let v₀ : V.object.domain := ⟨v.val,rvLabelImage_subset e.iso (P i) (hP i) v.property⟩
  have ht : liftLabelMap V.object (g p) = v₀ := by
    apply Subtype.ext
    exact (congrArg Prod.snd (hAgree i q p rfl)).symm
  change vfValue (LinearMap.toMatrix' L).det =
    (gammaMapValue U.form (liftLabelMap U.object p) / gammaMapValue V.form v₀).val at hJ
  rw [ht]
  exact hJ

end DiamondIntegral.Section6
