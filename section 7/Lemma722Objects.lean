import «section 7».PieceCombination
import «section 7».NormalizationComparison
import «section 7».TwoCellInput
import «section 6».MeasuredProperPreparation

/-! The objects of Lemma 7.22.

Let `A` be an object of `μVF^◇[n + 1]` over a base with support data.

1. **The prepared labels** (`prepObject`). Section 6's measured preparation
   (Lemma 6.21 with Remark 6.20, `measured_proper_preparation`) gives proper
   covariant RV data through which the form of `A` factors. Grafting them
   (`GraftObjects.graftObject`) gives an object `A'` whose form depends only on
   its labels (`prepObject_form_labels`), with a graft morphism `A → A'` that
   fixes every VF coordinate (`GraftObjects.graftMorphism`). This is the
   preparation of `ω` asked for in the referee's report R133.
2. **The normalized image** (`normObject`). For an object `A'` whose form
   depends only on its labels and a zero-centred normalization `D` of it, the
   normalized image `D(A')`, with the transported form, is again such an
   object. Its standard contractions have the classes of the contractions of
   `A'` with normalization `D` (`NormalizationComparison`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma722Objects
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.GraftObjects DiamondIntegral.Section7.LabelPieces
open DiamondIntegral.Section7.Corollary715 DiamondIntegral.Section7.NormalizationComparison

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M} (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVS : V ⊆ (T : Set M))
variable (hSV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n : ℕ}

/-! ### The prepared labels -/

section Prep
variable (A : VFObject (M := M) (T : Set M) (n + 1))

/-- Section 6's measured preparation of the form of `A`. -/
def prepData : MeasuredCoordinatePreparation (G := G) A.carrier (Fin.elim0) (fun i => i.elim0) A.form :=
  Classical.choice (measured_proper_preparation h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A.carrier A.proper
    Fin.elim0 (fun i => i.elim0) (fun i => i.elim0) A.form (object_levels hv A))

/-- The prepared labels. -/
def prepTau := rvProjection (prepData (G := G) h00 hc linear hκ hs hv V hV hVS hSV hnt hsmall hΓ A).map

theorem prepTau_covariant : ProperCovariant (prepTau (G := G) h00 hc linear hκ hs hv V hV hVS hSV hnt hsmall hΓ A) :=
  ProperCovariant.rvProjection _ ((prepData (G := G) h00 hc linear hκ hs hv V hV hVS hSV hnt hsmall hΓ A).special.properHomeomorphism
    h00 hc linear hκ hs hv hsmall hΓ).covariant

/-- **The object with the prepared labels grafted.** -/
def prepObject : VFObject (M := M) (T : Set M) (n + 1) :=
  graftObject h00 hc hκ hs hv A (prepTau (G := G) h00 hc linear hκ hs hv V hV hVS hSV hnt hsmall hΓ A)
    (prepTau_covariant h00 hc linear hκ hs hv V hV hVS hSV hnt hsmall hΓ A)

/-- The form of the prepared object depends only on its labels. -/
theorem prepObject_form_labels :
    ∀ p z : (prepObject (G := G) h00 hc linear hκ hs hv V hV hVS hSV hnt hsmall hΓ A).carrier,
      p.val.2 = z.val.2 →
        (prepObject (G := G) h00 hc linear hκ hs hv V hV hVS hSV hnt hsmall hΓ A).form p =
          (prepObject (G := G) h00 hc linear hκ hs hv V hV hVS hSV hnt hsmall hΓ A).form z := by
  intro p z he
  let Tm := prepData (G := G) h00 hc linear hκ hs hv V hV hVS hSV hnt hsmall hΓ A
  let τ := prepTau (G := G) h00 hc linear hκ hs hv V hV hVS hSV hnt hsmall hΓ A
  obtain ⟨p₀, rfl, -⟩ := graft_image_point hc A τ p
  obtain ⟨z₀, hz, -⟩ := graft_image_point hc A τ z
  subst hz
  change graftForm hc A τ (graft hc τ p₀) = graftForm hc A τ (graft hc τ z₀)
  rw [graftForm_graft, graftForm_graft]
  have hlab : (Tm.map p₀).val.2 = (Tm.map z₀).val.2 := by
    funext i
    have h := congrFun he (Fin.natAdd A.labels i)
    simpa only [graft_apply, Fin.append_right, τ, prepTau, rvProjection_apply] using h
  have hform := Tm.constant (Tm.map p₀).val (Tm.map p₀).property (Tm.map z₀).val (Tm.map z₀).property hlab
  rw [gammaFormExtension_at Tm.form (Tm.map p₀), gammaFormExtension_at Tm.form (Tm.map z₀)] at hform
  exact Subtype.ext ((Tm.transport p₀).symm.trans (hform.trans (Tm.transport z₀)))

/-- The graft of the prepared labels is a morphism, fixing every VF coordinate. -/
theorem prepMorphism :
    ∃ K : Morphism G A (prepObject (G := G) h00 hc linear hκ hs hv V hV hVS hSV hnt hsmall hΓ A),
      K.map = graft hc (prepTau (G := G) h00 hc linear hκ hs hv V hV hVS hSV hnt hsmall hΓ A) :=
  graftMorphism h00 hc linear hκ hs hv hsmall hΓ A _ (prepTau_covariant h00 hc linear hκ hs hv V hV hVS hSV hnt hsmall hΓ A)

end Prep

/-! ### The normalized image -/

section Norm
variable (A' : VFObject (M := M) (T : Set M) (n + 1)) (hω : ∀ p z : A'.carrier, p.val.2 = z.val.2 → A'.form p = A'.form z)
variable (D : ZeroCenteredData A'.carrier)

/-- The transported form on the normalized image. -/
abbrev normForm : Map D.map.image (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)) :=
  A'.form.comp (D.bijection.inverse (D.bijective h00))

theorem normForm_labels (hω : ∀ p z : A'.carrier, p.val.2 = z.val.2 → A'.form p = A'.form z) :
    ∀ p z : D.map.image, p.val.2 = z.val.2 → normForm h00 A' D p = normForm h00 A' D z := by
  intro p z he
  obtain ⟨p₀, rfl⟩ := (D.bijective h00).surjective p
  obtain ⟨z₀, rfl⟩ := (D.bijective h00).surjective z
  change A'.form (D.bijection.inverse (D.bijective h00) (D.bijection p₀)) =
    A'.form (D.bijection.inverse (D.bijective h00) (D.bijection z₀))
  rw [Map.inverse_apply, Map.inverse_apply]
  apply hω
  funext i
  have h := congrFun he (Fin.natAdd (n + 1) i)
  change Fin.append (fun j => branchTag (M := M) (D.core p₀.val j)) p₀.val.2 (Fin.natAdd (n + 1) i) =
    Fin.append (fun j => branchTag (M := M) (D.core z₀.val j)) z₀.val.2 (Fin.natAdd (n + 1) i) at h
  simpa only [Fin.append_right] using h

theorem normImage_finite :
    ∀ x : Fin (n + 1) → VF M, {t | (x, t) ∈ D.map.image.carrier}.Finite := by
  intro x
  have h := image_finite D (object_hFin A' Fin.elim0) x Fin.elim0
  refine h.subset fun t ht => ⟨ht, funext fun i => i.elim0⟩

/-- **The normalized image as an object.** -/
def normObject : VFObject (M := M) (T : Set M) (n + 1) :=
  objectOfLabelForm D.map.image (normForm h00 A' D) (D.image_properInvariant h00 hc hκ hs hv)
    (normForm_labels h00 A' D hω) (normImage_finite A' D)

theorem normObject_carrier : (normObject h00 hc hκ hs hv A' hω D).carrier = D.map.image := rfl

theorem normObject_form : (normObject h00 hc hκ hs hv A' hω D).form = normForm h00 A' D := rfl

theorem normObject_form_labels :
    ∀ p z : (normObject h00 hc hκ hs hv A' hω D).carrier, p.val.2 = z.val.2 →
      (normObject h00 hc hκ hs hv A' hω D).form p = (normObject h00 hc hκ hs hv A' hω D).form z :=
  normForm_labels h00 A' D hω

theorem normObject_doublyBounded : VFDoublyBounded (normObject h00 hc hκ hs hv A' hω D).carrier.carrier :=
  D.image_vfDoublyBounded

end Norm

end DiamondIntegral.Section7.Lemma722Objects
