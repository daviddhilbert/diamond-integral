import «section 6».UnaryMeasuredObstacles
import «section 6».SimultaneousRootStep
import «section 6».UnaryMeasuredSynchronizedFocusStep

/-! Measured unary preparation retains the actual synchronized finite
centripetal/regularization chain, so it can subsequently carry another
VF coordinate. All narrow components remain permitted restrictions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.UnaryRootFamily

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {k : ℕ} {S : Set M}

theorem exists_measured_synchronized_process_of_bound
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (N : ℕ) : ∀ {r : ℕ} (A : DefSet (rawMixedSpace (M := M) 1 r) S) (R : UnaryRootFamily A),
      ProperInvariant S A.carrier → VFDoublyBounded A.carrier → IsRVPullback A.carrier →
      (∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) →
      (∀ u, (R.fibre u).card ≤ N) →
      ∀ (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) (hCA : ∀ i, (C i).carrier ⊆ A.carrier),
      (∀ i, ProperInvariant S (C i).carrier) → (∀ i, UnaryRootControl (G := G) R (C i).carrier) →
      ∀ ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S),
      (∀ u γ, IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ}) →
      UnaryFormRootControl (G := G) R (gammaFormExtension ω) →
      ∃ T : UnaryMeasuredPreparation (G := G) A C hCA ω,
        SynchronizedCentripetalChain (G := G) (Fin k) A T.target T.map C := by
  induction N with
  | zero =>
      intro r A R hA hD hARV hTag hBound C hCA hC hControl ω hLevels hForm
      have hEmpty := R.roots_empty_of_bound_zero hBound
      refine ⟨{
        arity := r
        target := A
        map := Map.id A
        special := .identity A hA
        proper := hA
        doublyBounded := hD
        prepared := hARV
        tagged := hTag
        form := ω
        transport := fun _ => rfl
        constant := hForm.empty_roots_tag_constant hv hEmpty hARV hD hTag
        pieces := ?_
      },?_⟩
      · intro i
        have hCi := (hControl i).empty_roots_rvPullback hv hEmpty hARV hD (hCA i)
        have hg : SpecialCovariantChain (G := G) (C i) (C i) (Map.id (C i)) := .identity _ (hC i)
        have he := image_eq_of_surjective_liesOver (Map.id A) (Map.id (C i)) Function.surjective_id (hCA i) (fun _ => rfl)
        exact ⟨hg.restriction_of_liesOver h00 (Map.id A) (hCA i) (fun _ => rfl),by rw [← he]; exact hCi⟩
      · exact .identity A hA C hCA hC
  | succ N ih =>
      intro r A R hA hD hARV hTag hBound C hCA hC hControl ω hLevels hForm
      obtain ⟨X,hXAct,hXFocus⟩ := R.exists_focusData h00 hc hs hsmall hA hD hTag
      obtain ⟨δ,E,hcoord,hact,hfocus,hConst,hCut,hProtected⟩ := X.exists_measured_synchronized_family_step
        h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt C hCA hC ω hLevels
      have hact' : E.activeTags = R.activeTags := hact.trans hXAct
      have hfocus' (x u) : E.focus x u = Barycentre.mean (R.fibre u) := (hfocus x u).trans (hXFocus u)
      let E' (i : Fin k) : CentripetalData (G := G) (C i) := (hProtected i).choose
      have hE' (i) : ∀ p ∈ (C i).carrier, (E' i).point p = E.point p := (hProtected i).choose_spec.point
      let A₀ := (regularizeMap E.map.image).image
      let f₀ := stepMap E
      have hf₀ : Function.Bijective f₀ := stepMap_bijective E h00
      let C₀ (i : Fin k) := (f₀.restrict (hCA i)).image
      let g₀ (i : Fin k) := (f₀.restrict (hCA i)).toImage
      let ω₀ := ω.comp (f₀.inverse hf₀)
      have hStep : SpecialCovariantChain (G := G) A A₀ f₀ := stepMap_chain E h00 hc hκ hs hv
      have hEOld (i) : SpecialCovariantChain (G := G) (C i)
          (regularizeMap (E' i).map.image).image (stepMap (E' i)) := stepMap_chain (E' i) h00 hc hκ hs hv
      have hPointOld (i) (p : C i) : (stepMap (E' i) p).val = (f₀ ⟨p.val,hCA i p.property⟩).val :=
        congrArg regularize (hE' i p.val p.property)
      have hTarget (i) : (regularizeMap (E' i).map.image).image = C₀ i :=
        image_eq_of_surjective_liesOver f₀ (stepMap (E' i)) ((hEOld i).bijective h00).surjective (hCA i) (hPointOld i)
      have hg₀ (i) : SpecialCovariantChain (G := G) (C i) (C₀ i) (g₀ i) :=
        (hEOld i).restriction_of_liesOver h00 f₀ (hCA i) (hPointOld i)
      have hC₀A₀ (i) : (C₀ i).carrier ⊆ A₀.carrier := by
        rintro q ⟨p,hp⟩
        exact hp ▸ (f₀ ⟨p.val,hCA i p.property⟩).property
      have hA₀ : ProperInvariant S A₀.carrier := regularization_properInvariant h00 hc hκ hs hv _
        (E.image_properInvariant h00 hc hκ hs hv) E.image_vfDoublyBounded
      have hA₀D : VFDoublyBounded A₀.carrier := regularized_vfDoublyBounded E.image_vfDoublyBounded
      have hA₀RV : IsRVPullback A₀.carrier := regularization_rvPullback _ (E.unary_image_rvPullback hARV)
      have hTag₀ : ∀ p ∈ A₀.carrier, ∀ q ∈ A₀.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
        rw [show A₀.carrier = regularize '' E.map.image.carrier from regularization_carrier _]
        exact regularized_tagged _
      have hC₀ (i) : ProperInvariant S (C₀ i).carrier := by
        rw [← hTarget i]
        exact regularization_properInvariant h00 hc hκ hs hv _
          ((E' i).image_properInvariant h00 hc hκ hs hv) (E' i).image_vfDoublyBounded
      let Q := R.stepFamily E h00 hcoord hact' hfocus'
      have hControl₀ (i) : UnaryRootControl (G := G) Q (C₀ i).carrier :=
        R.root_control_step E (E' i) h00 hcoord hact' hfocus' (hCA i) (hE' i) (hControl i)
      have hForm₀ : UnaryFormRootControl (G := G) Q (gammaFormExtension ω₀) :=
        R.form_root_control_step E h00 hcoord hact' hfocus' δ hCut ω hConst hForm
      have hLevelsGeometry := hStep.gamma_levels_proper_geometry h00 hc linear hκ hs hv hsmall hΓ ω hLevels
      have hLevels₀ (u γ) : IsOpen {a : Fin 1 → VF M | (a,u) ∈ A₀.carrier ∧ gammaFormExtension ω₀ (a,u) = γ} :=
        ((hLevelsGeometry γ).clopen_fibres hv u).isOpen
      obtain ⟨T,hT⟩ := ih A₀ Q hA₀ hA₀D hA₀RV hTag₀ (R.stepFamily_bound E h00 hcoord hact' hfocus' N hBound)
        C₀ hC₀A₀ hC₀ hControl₀ ω₀ hLevels₀ hForm₀
      have hTransport₀ (p : A) : (ω₀ (f₀ p)).val = (ω p).val := by
        change (ω (f₀.inverse hf₀ (f₀ p))).val = (ω p).val
        rw [Map.inverse_apply]
      have hStrong : SynchronizedCentripetalChain (G := G) (Fin k) A A₀ f₀ C :=
        synchronized_centripetal_step h00 hc hκ hs hv E C E' (fun i => (hProtected i).choose_spec)
      exact ⟨T.precompose h00 C hCA f₀ hStep hg₀ hC₀A₀ ω ω₀ hTransport₀,
        .comp C hCA hStrong hT⟩

end DiamondIntegral.Section6.UnaryRootFamily
