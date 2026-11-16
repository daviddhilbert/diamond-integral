import «section 6».UnaryObstacleFamilies

/-! Simultaneous unary proper preparation on a doubly bounded tagged
RV-pullback. The finite root construction carries the root-free-disc
invariant through every protected step; no preparation input is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem image_eq_of_surjective_liesOver {n r s : ℕ}
    {A C : DefSet (rawMixedSpace (M := M) n r) S} {B D : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (g : Map C D) (hg : Function.Surjective g) (hCA : C.carrier ⊆ A.carrier)
    (hpoint : ∀ p : C, (g p).val = (f ⟨p.val,hCA p.property⟩).val) : D = (f.restrict hCA).image := by
  apply defSet_eq_of_carrier_eq
  ext q
  constructor
  · intro hq
    obtain ⟨p,hp⟩ := hg ⟨q,hq⟩
    exact ⟨p,(hpoint p).symm.trans (congrArg Subtype.val hp)⟩
  · rintro ⟨p,hp⟩
    have he : (g p).val = q := (hpoint p).trans hp
    exact he ▸ (g p).property

namespace UnaryRootFamily

variable {k : ℕ}

theorem exists_prepared_process_of_bound
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
      ∀ (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
        (hCA : ∀ i, (C i).carrier ⊆ A.carrier),
      (∀ i, ProperInvariant S (C i).carrier) → (∀ i, UnaryRootControl (G := G) R (C i).carrier) →
      ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ f : Map A B,
        SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧
        VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
        ∀ i, SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
          IsRVPullback (f.restrict (hCA i)).image.carrier := by
  induction N with
  | zero =>
      intro r A R hA hD hARV htag hb C hCA hC hControl
      refine ⟨r,A,Map.id A,.identity A hA,hA,hD,hARV,fun i => ?_⟩
      have hCiRV := (hControl i).empty_roots_rvPullback hv (R.roots_empty_of_bound_zero hb) hARV hD (hCA i)
      have hg : SpecialCovariantChain (G := G) (C i) (C i) (Map.id (C i)) := .identity _ (hC i)
      have he := image_eq_of_surjective_liesOver (Map.id A) (Map.id (C i)) Function.surjective_id (hCA i) (fun _ => rfl)
      exact ⟨hg.restriction_of_liesOver h00 (Map.id A) (hCA i) (fun _ => rfl),by rw [← he]; exact hCiRV⟩
  | succ N ih =>
      intro r A R hA hD hARV htag hb C hCA hC hControl
      obtain ⟨F,hFact,hFfocus⟩ := R.exists_focusData h00 hc hs hsmall hA hD htag
      obtain ⟨E,hcoord,hact,hfocus,hProtected⟩ := F.exists_protected_family_step h00 hc linear hκ hs hv V
        hsmall hΓ hV hVS hSV hnt C hCA hC
      have hact' : E.activeTags = R.activeTags := hact.trans hFact
      have hfocus' (x u) : E.focus x u = Barycentre.mean (R.fibre u) := (hfocus x u).trans (hFfocus u)
      let E' (i : Fin k) : CentripetalData (G := G) (C i) := (hProtected i).choose
      have hE' (i) : ∀ p ∈ (C i).carrier, (E' i).point p = E.point p := (hProtected i).choose_spec
      let A₀ := (regularizeMap E.map.image).image
      let f₀ := stepMap E
      let C₀ (i : Fin k) := (f₀.restrict (hCA i)).image
      let g₀ (i : Fin k) := (f₀.restrict (hCA i)).toImage
      have hstep : SpecialCovariantChain (G := G) A A₀ f₀ := stepMap_chain E h00 hc hκ hs hv
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
      obtain ⟨s,B,f,hchain,hB,hBD,hBRV,hPieces⟩ := ih A₀ Q hA₀ hA₀D hA₀RV htag₀
        (R.stepFamily_bound E h00 hcoord hact' hfocus' N hb) C₀ hC₀A₀ hC₀ hControl₀
      refine ⟨s,B,f.comp f₀,.comp hstep hchain,hB,hBD,hBRV,fun i => ?_⟩
      have hg : SpecialCovariantChain (G := G) (C i) (f.restrict (hC₀A₀ i)).image
          ((f.restrict (hC₀A₀ i)).toImage.comp (g₀ i)) := .comp (hg₀ i) (hPieces i).1
      have hpoint (p : C i) :
          (((f.restrict (hC₀A₀ i)).toImage.comp (g₀ i)) p).val =
            ((f.comp f₀) ⟨p.val,hCA i p.property⟩).val := rfl
      have he := image_eq_of_surjective_liesOver (f.comp f₀)
        ((f.restrict (hC₀A₀ i)).toImage.comp (g₀ i)) (hg.bijective h00).surjective (hCA i) hpoint
      exact ⟨hg.restriction_of_liesOver h00 (f.comp f₀) (hCA i) hpoint,by rw [← he]; exact (hPieces i).2⟩

end UnaryRootFamily

theorem unary_proper_preparation_of_doublyBounded_tagged {r k : ℕ}
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      ∀ i, SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
        IsRVPullback (f.restrict (hCA i)).image.carrier := by
  obtain ⟨R,hControl⟩ := exists_controlling_unary_rootFamily hc hv A C
  obtain ⟨N,hN⟩ := R.exists_uniform_bound hc hs hsmall
  have hb (u) : (R.fibre u).card ≤ N := by simpa only [R.rawFamily_labels] using hN (rvValues u)
  exact UnaryRootFamily.exists_prepared_process_of_bound h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt N
    A R hA hD hARV htag hb C hCA hC hControl

end DiamondIntegral.Section6
