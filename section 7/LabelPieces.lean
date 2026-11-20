import «section 7».RestrictContractions
import «section 7».GraftObjects
import «section 7».RelativeRestrict

/-! Objects with forms read on labels, and label pieces (for Lemma 7.22).

* `objectOfLabelForm`: a proper invariant set with finite RV fibres and a form
  depending only on the labels is an object of `μVF^◇[n]` (the form is constant
  on label fibres, so any named invariance radius serves for it).
* `pieceObject A L`: the restriction of an object `A` to the labels in a
  definable set `L` (Section 6 `focusActive`), with the restricted form. It is
  label-saturated in `A` (`pieceObject_saturated`), so every standard
  contraction of `A` restricts to it (`RestrictContractions.restrictContraction`),
  and the classes of complementary pieces add up
  (`RestrictContractions.cls_headStart_zero_split`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.LabelPieces
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section7.RestrictContractions DiamondIntegral.Section7.RelativeRestrict

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

/-- **An object with a form read on labels.** -/
def objectOfLabelForm (X : DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)) (hX : ProperInvariant S X.carrier)
    (hω : ∀ p z : X, p.val.2 = z.val.2 → ω p = ω z) (hfin : ∀ x : Fin n → VF M, {t | (x, t) ∈ X.carrier}.Finite) :
    VFObject (M := M) S n where
  labels := r
  carrier := X
  form := ω
  proper := hX
  formCovariant := fun t => by
    obtain ⟨α, hα, -⟩ := hX.radii t
    refine ⟨α, hα, fun x y hx hy _ => ?_⟩
    unfold gammaMapValue
    rw [hω ⟨(x, t), hx⟩ ⟨(y, t), hy⟩ rfl]
  finiteRV := hfin

theorem objectOfLabelForm_carrier (X : DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)) (hX : ProperInvariant S X.carrier)
    (hω : ∀ p z : X, p.val.2 = z.val.2 → ω p = ω z) (hfin : ∀ x : Fin n → VF M, {t | (x, t) ∈ X.carrier}.Finite) :
    (objectOfLabelForm X ω hX hω hfin).carrier = X := rfl

/-- **The piece of an object over a definable set of labels.** -/
def pieceObject (A : VFObject (M := M) S n) (L : DefSet (rawRVSpace (M := M) A.labels) S) : VFObject (M := M) S n where
  labels := A.labels
  carrier := focusActive A.carrier L
  form := A.form.restrict (fun _ h => h.1)
  proper := properInvariant_focusActive A.carrier L A.proper
  formCovariant := fun t => by
    obtain ⟨α, hα, hcov⟩ := A.formCovariant t
    exact ⟨α, hα, fun x y hx hy hxy => hcov x y hx.1 hy.1 hxy⟩
  finiteRV := fun x => (A.finiteRV x).subset (fun _ h => h.1)

theorem pieceObject_carrier (A : VFObject (M := M) S n) (L : DefSet (rawRVSpace (M := M) A.labels) S) :
    (pieceObject A L).carrier = focusActive A.carrier L := rfl

theorem pieceObject_saturated (A : VFObject (M := M) S n) (L : DefSet (rawRVSpace (M := M) A.labels) S) :
    LabelSaturated (pieceObject A L).carrier A.carrier :=
  ⟨fun _ h => h.1, fun _ _ q hq he hp => ⟨hq, he ▸ hp.2⟩⟩

/-- The complementary set of labels. -/
def complLabels {m : ℕ} (L : DefSet (rawRVSpace (M := M) m) S) : DefSet (rawRVSpace (M := M) m) S :=
  ⟨L.carrierᶜ, L.definable.compl _⟩

theorem pieces_disjoint (A : VFObject (M := M) S n) (L : DefSet (rawRVSpace (M := M) A.labels) S) :
    Disjoint (pieceObject A L).carrier.carrier (pieceObject A (complLabels L)).carrier.carrier :=
  Set.disjoint_left.mpr fun _ h h' => h'.2 h.2

theorem pieces_cover (A : VFObject (M := M) S n) (L : DefSet (rawRVSpace (M := M) A.labels) S) :
    A.carrier.carrier ⊆ (pieceObject A L).carrier.carrier ∪ (pieceObject A (complLabels L)).carrier.carrier := by
  intro p hp
  by_cases h : p.2 ∈ L.carrier
  · exact Or.inl ⟨hp, h⟩
  · exact Or.inr ⟨hp, h⟩

end DiamondIntegral.Section7.LabelPieces
