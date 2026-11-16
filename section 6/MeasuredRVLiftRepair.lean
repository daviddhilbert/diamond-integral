import «section 6».SmallLiftLabelImages
import «section 6».EverywhereMeasuredRVLiftData

/-! In every degree, a chosen almost-everywhere measured lift can be
repaired on whole old-label polydiscs by an actual everywhere measured
lift on the exceptional label domain. All full derivatives transfer
through fixed-label agreement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem exists_repaired_measured_rv_lift
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (f : Map (rvLift U.object) (rvLift V.object)) (hf : Function.Bijective f)
    (hlabel : ∀ p, e.iso.hom.map.graph p.val.2 (f p).val.2)
    (E : DefSet (rawMixedSpace (M := M) n U.object.arity) S)
    (hE : E.carrier ⊆ (rvLift U.object).carrier)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (hCover : (badRVLiftLabels U.object E hE).carrier ⊆ D.carrier)
    (g₀ : EverywhereMeasuredRVLift (e.restrict D hD))
    (hgood : ∀ p : rvLift U.object, p.val ∉ E.carrier →
      ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object (f p))).val) :
    Nonempty (EverywhereMeasuredRVLift e) := by
  let g := g₀.map
  have hg := g₀.bijective
  have hglab := g₀.labels
  have hgm := g₀.measure
  let D₂ := U.object.domain.sdiff D
  let hD₂ : D₂.carrier ⊆ U.object.domain.carrier := Set.sdiff_subset
  obtain ⟨f',hf',hfagree⟩ := exists_restricted_actual_lift e.iso D₂ hD₂ f hf hlabel
  let P : Bool → DefSet (rawRVSpace (M := M) U.object.arity) S := fun i => if i then D else D₂
  have hP : ∀ i, (P i).carrier ⊆ U.object.domain.carrier := by
    intro i
    cases i
    · exact hD₂
    · exact hD
  have hcover (u : U.object.domain) : ∃ i, u.val ∈ (P i).carrier := by
    by_cases hu : u.val ∈ D.carrier
    · exact ⟨true,hu⟩
    · exact ⟨false,u.property,hu⟩
  have hdisj (i j : Bool) (z) : z ∈ (P i).carrier → z ∈ (P j).carrier → i = j := by
    cases i <;> cases j
    · exact fun _ _ => rfl
    · exact fun hu hd => (hu.2 hd).elim
    · exact fun hd hu => (hu.2 hd).elim
    · exact fun _ _ => rfl
  let F : ∀ i, Map (rvLift (U.object.restrict (P i) (hP i)))
      (rvLift (V.object.restrict (e.iso.hom.map.restrict (hP i)).image (rvLabelImage_subset e.iso (P i) (hP i)))) :=
    fun i => by
      cases i
      · exact f'
      · exact g
  have hF : ∀ i, Function.Bijective (F i) := by
    intro i
    cases i
    · exact hf'
    · exact hg
  have hFlab (i) (p : rvLift (U.object.restrict (P i) (hP i))) :
      e.iso.hom.map.graph p.val.2 (F i p).val.2 := by
    cases i
    · let q : rvLift U.object := ⟨p.val,((rvLift_restrict_mem_iff U.object D₂ hD₂ _).mp p.property).1⟩
      exact (hfagree p q rfl).symm ▸ hlabel q
    · obtain ⟨u,hu,hv⟩ := hglab p
      exact ⟨⟨u.val,hD u.property⟩,hu,hv⟩
  obtain ⟨H,hH,hHlab,hHagree⟩ := exists_glued_label_lift e.iso P hP hcover hdisj F hF hFlab
  refine ⟨⟨H,hH,hHlab,fun p => ?_⟩⟩
  by_cases hpD : p.val.2 ∈ D.carrier
  · let q : rvLift (U.object.restrict D hD) :=
      ⟨p.val,(rvLift_restrict_mem_iff U.object D hD _).mpr ⟨p.property,hpD⟩⟩
    obtain ⟨L,hL,hJ⟩ := hgm q
    refine ⟨L,mixedDerivative_of_label_restriction (U := U.object) (V := V.object)
      D hD g H q p rfl (hHagree true) hL,?_⟩
    let v := liftLabelMap (V.restrict (e.iso.hom.map.restrict hD).image (rvLabelImage_subset e.iso D hD)).object (g q)
    let v₀ : V.object.domain := ⟨v.val,rvLabelImage_subset e.iso D hD v.property⟩
    have ht : liftLabelMap V.object (H p) = v₀ := by
      apply Subtype.ext
      exact (congrArg (fun z : Mixed M n V.object.arity => z.2) (hHagree true q p rfl)).symm
    change vfValue (LinearMap.toMatrix' L).det =
      (gammaMapValue U.form (liftLabelMap U.object p) /
        gammaMapValue V.form v₀).val at hJ
    rw [ht]
    exact hJ
  · have hagree (p' : rvLift U.object) (he : p'.val.2 = p.val.2) : (f p').val = (H p').val := by
      have hp'D : p'.val.2 ∉ D.carrier := he ▸ hpD
      let q' : rvLift (U.object.restrict D₂ hD₂) :=
        ⟨p'.val,(rvLift_restrict_mem_iff U.object D₂ hD₂ _).mpr
          ⟨p'.property,(liftLabelMap U.object p').property,hp'D⟩⟩
      exact (hfagree q' p' rfl).symm.trans (hHagree false q' p' rfl)
    obtain ⟨L,hL,hJ⟩ := hgood p (by
      intro hpE
      exact hpD (hCover ⟨⟨p.val,hpE⟩,rfl⟩))
    refine ⟨L,mixedDerivative_of_label_agreement f H p hagree hL,?_⟩
    have he : f p = H p := Subtype.ext (hagree p rfl)
    rw [← he]
    exact hJ

end DiamondIntegral.Section6
