import «section 7».PullbackStages
import «section 6».RVGraftingHomeomorphism
import «section 6».DiamondGroupoidMaps

/-! Grafting RV labels onto an object of `μVF^◇[n]` (for Lemma 7.22).

Let `A` be an object of `μVF^◇[n]` and `τ : A → D ⊆ RV^q` a proper covariant
definable map. The graft `p ↦ (p, τ(p))` (Section 6 `graft`) appends the values
of `τ` as new labels. Its image, with the form of `A` carried over, is again an
object of `μVF^◇[n]` (`graftObject`): proper invariant by Section 6
`graft_properInvariant`, with finite RV fibres because the new labels are
determined by the old ones, and with a covariant form because it is read on the
old labels. The graft fixes every VF coordinate, so it is relatively unary in
every coordinate (`graft_relativelyUnary`). It has unit derivative and keeps the
form, so it underlies a morphism of `μVF^◇[n]` (`graftMorphism`).

Lemma 7.22 grafts twice: first the labels through which the form factors
(Remark 6.20, Lemma 6.21), then the RV point of the standard contraction given
by Lemma 7.20, so that each label fibre of the result is a `2`-cell. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.GraftObjects
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGroupoid DiamondIntegral.Section7.PullbackStages

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {S : Set M} (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable {n q : ℕ} (A : VFObject (M := M) S n) {D : DefSet (rawMixedSpace (M := M) 0 q) S}
variable (τ : Map A.carrier D) (hτ : ProperCovariant τ)

/-- The form of the graft: the form of `A` at the original point. -/
def graftForm : Map (graftMap hc τ).image (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  A.form.comp ((graft hc τ).inverse (graft_bijective hc τ))

theorem graftForm_graft (p : A.carrier) : graftForm hc A τ (graft hc τ p) = A.form p := by
  change A.form ((graft hc τ).inverse (graft_bijective hc τ) (graft hc τ p)) = _
  rw [Map.inverse_apply]

/-- A point of the graft image is the graft of the point given by its VF
coordinates and its old labels. -/
theorem graft_image_point (z : (graftMap hc τ).image) :
    ∃ p : A.carrier, graft hc τ p = z ∧ p.val = (z.val.1, fun i => z.val.2 (Fin.castAdd q i)) := by
  obtain ⟨p, hp⟩ := (graft_bijective hc τ).surjective z
  refine ⟨p, hp, ?_⟩
  have h : ((p.val.1, Fin.append p.val.2 (τ p).val.2) : Mixed M n (A.labels + q)) = z.val :=
    (graft_apply hc τ p).symm.trans (congrArg Subtype.val hp)
  have h1 : p.val.1 = z.val.1 := congrArg Prod.fst h
  have h2 : Fin.append p.val.2 (τ p).val.2 = z.val.2 := congrArg Prod.snd h
  refine Prod.ext h1 (funext fun i => ?_)
  have := congrFun h2 (Fin.castAdd q i)
  simpa only [Fin.append_left] using this

include h00 hκ hv hτ in
/-- **The grafted object.** -/
def graftObject : VFObject (M := M) S n where
  labels := A.labels + q
  carrier := (graftMap hc τ).image
  form := graftForm hc A τ
  proper := graft_properInvariant h00 hc hκ hs hv τ A.proper hτ
  formCovariant := fun t => by
    obtain ⟨α, hα, hcov⟩ := A.formCovariant (fun i => t (Fin.castAdd q i))
    refine ⟨α, fun i => (hα i).mono (Set.union_subset_union_right _ (range_rvValues_comp_subset t _)),
      fun x y hx hy hxy => ?_⟩
    obtain ⟨p, hp, hpv⟩ := graft_image_point hc A τ ⟨(x, t), hx⟩
    obtain ⟨p', hp', hpv'⟩ := graft_image_point hc A τ ⟨(y, t), hy⟩
    have hx' : ((x, fun i => t (Fin.castAdd q i)) : Mixed M n A.labels) ∈ A.carrier.carrier := hpv ▸ p.property
    have hy' : ((y, fun i => t (Fin.castAdd q i)) : Mixed M n A.labels) ∈ A.carrier.carrier := hpv' ▸ p'.property
    have e1 : p = ⟨_, hx'⟩ := Subtype.ext hpv
    have e2 : p' = ⟨_, hy'⟩ := Subtype.ext hpv'
    unfold gammaMapValue
    rw [← hp, ← hp', graftForm_graft, graftForm_graft, e1, e2]
    exact hcov x y hx' hy' hxy
  finiteRV := fun x => by
    refine Set.Finite.of_finite_image (f := fun t => fun i => t (Fin.castAdd q i))
      ((A.finiteRV x).subset ?_) ?_
    · rintro _ ⟨t, ht, rfl⟩
      obtain ⟨p, _, hpv⟩ := graft_image_point hc A τ ⟨(x, t), ht⟩
      show ((x, fun i => t (Fin.castAdd q i)) : Mixed M n A.labels) ∈ A.carrier.carrier
      exact (show p.val = ((x, fun i => t (Fin.castAdd q i)) : Mixed M n A.labels) from hpv) ▸ p.property
    · intro t ht t' ht' he
      obtain ⟨p, hp, hpv⟩ := graft_image_point hc A τ ⟨(x, t), ht⟩
      obtain ⟨p', hp', hpv'⟩ := graft_image_point hc A τ ⟨(x, t'), ht'⟩
      have hpp : p = p' := Subtype.ext (hpv.trans ((congrArg (Prod.mk x) he).trans hpv'.symm))
      subst hpp
      have h1 := congrArg (fun z : (graftMap hc τ).image => z.val.2) (hp.symm.trans hp')
      exact h1

theorem graftObject_carrier :
    (graftObject h00 hc hκ hs hv A τ hτ).carrier = (graftMap hc τ).image := rfl

/-- The graft fixes every VF coordinate. -/
theorem graft_relativelyUnary (i : Fin n) : VFRelativelyUnary (graft hc τ) i i := by
  intro p k _
  simp only [Equiv.symm_apply_apply]
  rfl

include linear hsmall hΓ in
/-- **The graft is a morphism of `μVF^◇[n]`.** -/
theorem graftMorphism :
    ∃ K : Morphism G A (graftObject h00 hc hκ hs hv A τ hτ), K.map = graft hc τ := by
  let g : Map A.carrier (graftObject h00 hc hκ hs hv A τ hτ).carrier := graft hc τ
  have homeo : ProperCovariantHomeomorphism (G := G) g :=
    graft_properHomeomorphism (G := G) h00 hc linear hκ hs hv hsmall hΓ τ A.proper hτ
  have hunary : n = 0 ∨ ∃ i : Fin n, VFUnaryRelativeAt g i := by
    rcases n with _ | n
    · exact Or.inl rfl
    · exact Or.inr ⟨0, (vfRelativelyUnary_self _ _).mp (graft_relativelyUnary hc A τ 0)⟩
  refine morphism_of_step h00 hc hs hsmall g homeo hunary (fun p _ => ?_)
  obtain ⟨L, hL, hdet⟩ := graft_unit_derivative hc hv τ hτ p
  refine ⟨L, hL, ?_⟩
  rw [hdet]
  change vfValue 1 = (gammaMapValue A.form p / gammaMapValue (graftForm hc A τ) (graft hc τ p)).val
  unfold gammaMapValue
  rw [graftForm_graft, div_self']
  change Values.vfValueHom 1 = Values.gammaValHom 1
  rw [map_one, map_one]

end DiamondIntegral.Section7.GraftObjects
