import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowCoreFormCompatibility
import «section 6».RowCoreGammaForms
import «section 6».RowFormCompatibleFocusSteps
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowMeasuredUnaryContextSteps
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredCompatibleExistence
import «section 6».RowUnaryMeasuredCompatiblePreparation
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredObstacles
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration
import «section 6».RowMeasuredUnaryValueContextStep
import «section 6».RowExactGammaTransport
import «section 6».ProtectedUnaryContextPreparation
import «section 6».UnaryValueControlStep

/-! (Row-form version for Remark 6.20, translated from `MeasuredUnaryValueContextPreparation`.)
 Terminating preparation of complete arbitrary data values, together
with a form-compatible actual ambient lift protecting the full higher-dimensional
partition. A single named radius controls the rows; RV output values
need not be bounded or finite. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {T : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
namespace UnaryRootFamily
variable {k l m : ℕ} {j : Fin m}
theorem exists_value_prepared_form_compatible_context_process_of_bound_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (N : ℕ) : ∀ {r : ℕ} (A : DefSet (rawMixedSpace (M := M) 1 r) S) (R : UnaryRootFamily A),
      ProperInvariant S A.carrier → VFDoublyBounded A.carrier → IsRVPullback A.carrier →
      (∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) →
      (∀ u, (R.fibre u).card ≤ N) →
      ∀ (ρ : Gamma M) (hρ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {ρ}})
        (ω : Mixed M 1 r → T) (defaultValue : T),
      (∀ u,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
        Congruent (fun _ => ρ) a b → ω (a,u)=ω (b,u)) →
      UnaryValueRootControl (G := G) R ω →
      ∀ (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
        (hCA : ∀ i, (C i).carrier ⊆ A.carrier),
      (∀ i, ProperInvariant S (C i).carrier) → (∀ i, UnaryRootControl (G := G) R (C i).carrier) →
      ∀ (X : UnaryPreparationContext A j)
        (P : Fin l → DefSet (rawMixedSpace (M := M) m X.arity) S)
        (hPX : ∀ i, (P i).carrier ⊆ X.source.carrier),
      (∀ i, ProperInvariant S (P i).carrier) →
      ∀ θ : RowFormOn X.source qR,
      (∀ u γ,IsOpen {x : Fin m → VF M | (x,u) ∈ X.source.carrier ∧ rowFormExtension θ (x,u)=γ}) →
      ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ f : Map A B,∃ η : Mixed M 1 s → T,
        SynchronizedCentripetalChain (G := G) (Fin k) A B f C ∧ ProperInvariant S B.carrier ∧
        VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
        (∀ p ∈ B.carrier, ∀ q ∈ B.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) ∧
        (∀ i, SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
          IsRVPullback (f.restrict (hCA i)).image.carrier) ∧
        ∃ U : UnaryContextLift (G := G) X f P,
        FormCompatibleSynchronizedChainRow (G := G) (Fin l) X.source U.target.source U.map P θ ∧
        (∀ p : A,η (f p).val=ω p.val) ∧
        (∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → η p=η q) := by
  induction N with
  | zero =>
      intro r A R hA hD hARV htag hb ρ hρ ω defaultValue hConst hValue C hCA hC hControl X P hPX hP θ hLevels
      refine ⟨r,A,Map.id A,ω,.identity A hA C hCA hC,hA,hD,hARV,htag,?_,
        UnaryContextLift.identity X P hPX hP,.identity X.source X.proper P hPX hP θ,(fun _ => rfl),
        hValue.empty_roots_tag_constant hv (R.roots_empty_of_bound_zero hb) hARV hD htag⟩
      intro i
      have hCiRV := (hControl i).empty_roots_rvPullback hv (R.roots_empty_of_bound_zero hb) hARV hD (hCA i)
      have hg : SpecialCovariantChain (G := G) (C i) (C i) (Map.id (C i)) := .identity _ (hC i)
      have he := image_eq_of_surjective_liesOver (Map.id A) (Map.id (C i)) Function.surjective_id (hCA i) (fun _ => rfl)
      exact ⟨hg.restriction_of_liesOver h00 (Map.id A) (hCA i) (fun _ => rfl),by rw [← he]; exact hCiRV⟩
  | succ N ih =>
      intro r A R hA hD hARV htag hb ρ hρ ω defaultValue hConst hValue C hCA hC hControl X P hPX hP θ hLevels
      obtain ⟨F,hFact,hFfocus⟩ := R.exists_focusData h00 hc hs hsmall hA hD htag
      obtain ⟨E,hcoord,hact,hfocus,hCut,hProtected,H₀,hH₀⟩ := F.exists_form_compatible_protected_context_step_above_radius_row h00 hc linear hκ hs hv V
        hsmall hΓ hV hVS hSV hnt X ρ hρ C hCA hC P hPX hP θ hLevels
      let P₀ (i) := (H₀.map.restrict (hPX i)).image
      have hact' : E.activeTags = R.activeTags := hact.trans hFact
      have hfocus' (x u) : E.focus x u = Barycentre.mean (R.fibre u) := (hfocus x u).trans (hFfocus u)
      let E' (i : Fin k) : CentripetalData (G := G) (C i) := (hProtected i).choose
      have hE' (i) : ∀ p ∈ (C i).carrier, (E' i).point p = E.point p := (hProtected i).choose_spec.point
      let A₀ := (regularizeMap E.map.image).image
      let f₀ := stepMap E
      let C₀ (i : Fin k) := (f₀.restrict (hCA i)).image
      let g₀ (i : Fin k) := (f₀.restrict (hCA i)).toImage
      have hstep : SynchronizedCentripetalChain (G := G) (Fin k) A A₀ f₀ C :=
        synchronized_centripetal_step h00 hc hκ hs hv E C E' (fun i => (hProtected i).choose_spec)
      have hEOld (i) : SpecialCovariantChain (G := G) (C i)
          (regularizeMap (E' i).map.image).image (stepMap (E' i)) := stepMap_chain (E' i) h00 hc hκ hs hv
      have hpointOld (i) (p : C i) : (stepMap (E' i) p).val = (f₀ ⟨p.val,hCA i p.property⟩).val :=
        congrArg regularize (hE' i p.val p.property)
      have htarget (i) : (regularizeMap (E' i).map.image).image = C₀ i :=
        image_eq_of_surjective_liesOver f₀ (stepMap (E' i)) ((hEOld i).bijective h00).surjective
          (hCA i) (hpointOld i)
      have hg₀ (i) : SpecialCovariantChain (G := G) (C i) (C₀ i) (g₀ i) :=
        (hEOld i).restriction_of_liesOver h00 f₀ (hCA i) (hpointOld i)
      have hC₀A₀ (i) : (C₀ i).carrier ⊆ A₀.carrier := by
        rintro q ⟨p,hp⟩
        exact hp ▸ (f₀ ⟨p.val,hCA i p.property⟩).property
      have hA₀ : ProperInvariant S A₀.carrier := regularization_properInvariant h00 hc hκ hs hv _
        (E.image_properInvariant h00 hc hκ hs hv) E.image_vfDoublyBounded
      have hA₀D : VFDoublyBounded A₀.carrier := regularized_vfDoublyBounded E.image_vfDoublyBounded
      have hA₀RV : IsRVPullback A₀.carrier := regularization_rvPullback _ (E.unary_image_rvPullback hARV)
      have htag₀ : ∀ p ∈ A₀.carrier, ∀ q ∈ A₀.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
        rw [show A₀.carrier = regularize '' E.map.image.carrier from regularization_carrier _]
        exact regularized_tagged _
      have hC₀ (i) : ProperInvariant S (C₀ i).carrier := by
        rw [← htarget i]
        exact regularization_properInvariant h00 hc hκ hs hv _
          ((E' i).image_properInvariant h00 hc hκ hs hv) (E' i).image_vfDoublyBounded
      let Q := R.stepFamily E h00 hcoord hact' hfocus'
      have hControl₀ (i) : UnaryRootControl (G := G) Q (C₀ i).carrier :=
        R.root_control_step E (E' i) h00 hcoord hact' hfocus' (hCA i) (hE' i) (hControl i)
      have hf₀ : Function.Bijective f₀ := stepMap_bijective E h00
      let ω₀ (p : Mixed M 1 (1+(1+r))) : T :=
        if hp : p ∈ A₀.carrier then ω (f₀.inverse hf₀ ⟨p,hp⟩).val else defaultValue
      have hTransport₀ (p : A) : ω₀ (f₀ p).val=ω p.val := by
        unfold ω₀
        split_ifs with hp
        · change ω (f₀.inverse hf₀ (f₀ p)).val=ω p.val
          rw [Map.inverse_apply]
        · exact (hp (f₀ p).property).elim
      have hConst₀ := step_transport_uniform_constancy E h00 ρ ω ω₀ hTransport₀ hConst
      have hValue₀ := value_root_control_step R E h00 hcoord hact' hfocus' ρ hCut ω ω₀ hTransport₀ hConst hValue
      have hSpecial₀ := hH₀.toSynchronizedRow.toChain.toSpecial
      let θ₀ := θ.comp (H₀.map.inverse (hSpecial₀.bijective h00))
      have hFormTransport₀ (p : X.source) : (θ₀ (H₀.map p)).val=(θ p).val := by
        change (θ (H₀.map.inverse _ (H₀.map p))).val=(θ p).val
        rw [Map.inverse_apply]
      have hLevels₀ := hSpecial₀.exact_gamma_levels_open_row h00 hc linear hκ hs hv hsmall hΓ θ hLevels θ₀ hFormTransport₀
      obtain ⟨s,B,f,η,hchain,hB,hBD,hBRV,hBtag,hPieces,H,hH,hTransport,hTagConst⟩ := ih A₀ Q hA₀ hA₀D hA₀RV htag₀
        (R.stepFamily_bound E h00 hcoord hact' hfocus' N hb) ρ hρ ω₀ defaultValue hConst₀ hValue₀ C₀ hC₀A₀ hC₀ hControl₀
        H₀.target P₀ (H₀.image_subset hPX) (H₀.image_proper h00 hc linear hκ hs hv hsmall hΓ hPX) θ₀ hLevels₀
      refine ⟨s,B,f.comp f₀,η,.comp C hCA hstep hchain,hB,hBD,hBRV,hBtag,?_,H₀.comp hPX H,.comp P hPX hH₀ θ₀ hFormTransport₀ hH,(fun p => (hTransport (f₀ p)).trans (hTransport₀ p)),hTagConst⟩
      intro i
      have hg : SpecialCovariantChain (G := G) (C i) (f.restrict (hC₀A₀ i)).image
          ((f.restrict (hC₀A₀ i)).toImage.comp (g₀ i)) := .comp (hg₀ i) (hPieces i).1
      have hpoint (p : C i) :
          (((f.restrict (hC₀A₀ i)).toImage.comp (g₀ i)) p).val =
            ((f.comp f₀) ⟨p.val,hCA i p.property⟩).val := rfl
      have he := image_eq_of_surjective_liesOver (f.comp f₀)
        ((f.restrict (hC₀A₀ i)).toImage.comp (g₀ i)) (hg.bijective h00).surjective (hCA i) hpoint
      exact ⟨hg.restriction_of_liesOver h00 (f.comp f₀) (hCA i) hpoint,by rw [← he]; exact (hPieces i).2⟩

end UnaryRootFamily
end DiamondIntegral.Section6
