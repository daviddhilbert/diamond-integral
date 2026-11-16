import «section 6».MeasuredRVRestrictions
import «section 6».InitialPreparation

/-! Repair an almost-everywhere unary measured lift on whole exceptional
old-label discs. The replacement is constructed on its finite label
family, and the complementary branch retains the chosen lift. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem mixedDerivative_of_label_agreement {n r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f g : Map A B) (p : A)
    (hagree : ∀ q : A, q.val.2 = p.val.2 → (f q).val = (g q).val)
    {L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M)}
    (hL : HasMixedVFDerivativeAt f p L) : HasMixedVFDerivativeAt g p L := by
  obtain ⟨F,⟨ρ,hρ⟩,hD⟩ := hL
  refine ⟨F,⟨ρ,fun x hx => ?_⟩,hD⟩
  obtain ⟨hxA,hxF⟩ := hρ x hx
  refine ⟨hxA,?_⟩
  rw [← hagree ⟨(x,p.val.2),hxA⟩ rfl,hxF,congrArg Prod.snd (hagree p rfl)]

theorem exists_repaired_unary_measured_lift
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : Set M) (hW : ∀ a ∈ W, iVF a) (hWS : W ⊆ S) (hSW : S ⊆ algebraicClosureSet W)
    (hnt : ∃ x : vfAlgebraicClosureField W, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) {U V : MeasuredRVObject (M := M) S 1}
    (e : MeasuredRVIso U V) (f : Map (rvLift U.object) (rvLift V.object))
    (hf : Function.Bijective f) (hlabel : ∀ p, e.iso.hom.map.graph p.val.2 (f p).val.2)
    (E : DefSet (rawMixedSpace (M := M) 1 U.object.arity) S)
    (hE : E.carrier ⊆ (rvLift U.object).carrier) (hDim : vfDim (rawRVSpace (M := M) 1) E < 1)
    (hgood : ∀ p : rvLift U.object, p.val ∉ E.carrier →
      ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object (f p))).val) :
    ∃ F : Map (rvLift U.object) (rvLift V.object), Function.Bijective F ∧
      (∀ p, e.iso.hom.map.graph p.val.2 (F p).val.2) ∧
      ∀ p, ∃ L, HasMixedVFDerivativeAt F p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object (F p))).val := by
  let D := unaryBadLiftLabels U E hE
  let hD := unaryBadLiftLabels_subset U E hE
  have hDF := unaryBadLiftLabels_finite hc hs hsmall U E hE hDim
  obtain ⟨g,hg,hglab,hgm⟩ := exists_finite_unary_measured_rv_lift hc h00 hs hv W hW hWS hSW hnt hsmall
    (e.restrict D hD) hDF
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
  refine ⟨H,hH,hHlab,fun p => ?_⟩
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
      exact (congrArg (fun z : Mixed M 1 V.object.arity => z.2) (hHagree true q p rfl)).symm
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
    obtain ⟨L,hL,hJ⟩ := hgood p (unaryBadLiftLabels_cover U E hE p hpD)
    refine ⟨L,mixedDerivative_of_label_agreement f H p hagree hL,?_⟩
    have he : f p = H p := Subtype.ext (hagree p rfl)
    rw [← he]
    exact hJ

end DiamondIntegral.Section6
