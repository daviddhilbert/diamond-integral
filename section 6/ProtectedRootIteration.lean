import «section 6».SpecialCovariantRestrictions
import «section 6».UnaryPullbackPreservation

/-! The finite root process can simultaneously protect any finite family
of proper invariant subsets. Their literal restrictions remain special
covariant chains. The final RV-preparation predicate is a separate
obligation and is not asserted by this construction theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem target_subset_of_liesOver {n r s : ℕ}
    {A C : DefSet (rawMixedSpace (M := M) n r) S} {B D : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (g : Map C D) (hg : Function.Surjective g) (hCA : C.carrier ⊆ A.carrier)
    (hpoint : ∀ p : C, (g p).val = (f ⟨p.val,hCA p.property⟩).val) : D.carrier ⊆ B.carrier := by
  intro q hq
  obtain ⟨p,hp⟩ := hg ⟨q,hq⟩
  have he : (f ⟨p.val,hCA p.property⟩).val = q := (hpoint p).symm.trans (congrArg Subtype.val hp)
  exact he ▸ (f ⟨p.val,hCA p.property⟩).property

theorem regularized_vfDoublyBounded {n r : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} (hA : VFDoublyBounded A.carrier) :
    VFDoublyBounded (regularizeMap A).image.carrier := by
  obtain ⟨γ,hγ⟩ := hA
  refine ⟨γ,?_⟩
  rw [regularization_carrier]
  rintro _ ⟨p,hp,rfl⟩ i
  exact hγ p hp i

namespace UnaryRootFamily

variable {k : ℕ}

theorem exists_protected_process_of_bound
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (N : ℕ) : ∀ {r : ℕ} (A : DefSet (rawMixedSpace (M := M) 1 r) S) (R : UnaryRootFamily A),
      ProperInvariant S A.carrier → VFDoublyBounded A.carrier →
      (∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) →
      (∀ u, (R.fibre u).card ≤ N) →
      ∀ (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
        (hCA : ∀ i, (C i).carrier ⊆ A.carrier), (∀ i, ProperInvariant S (C i).carrier) →
      ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ f : Map A B,
        UnaryRootProcess (G := G) A R B f ∧ SpecialCovariantChain (G := G) A B f ∧
        ProperInvariant S B.carrier ∧ VFDoublyBounded B.carrier ∧
        ∀ i, ∃ D : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ g : Map (C i) D,
          SpecialCovariantChain (G := G) (C i) D g ∧
            ∀ p : C i, (g p).val = (f ⟨p.val,hCA i p.property⟩).val := by
  induction N with
  | zero =>
      intro r A R hA hD htag hb C hCA hC
      refine ⟨r,A,Map.id A,.done A R hA (R.roots_empty_of_bound_zero hb),.identity A hA,hA,hD,fun i => ?_⟩
      exact ⟨C i,Map.id _,.identity _ (hC i),fun _ => rfl⟩
  | succ N ih =>
      intro r A R hA hD htag hb C hCA hC
      obtain ⟨F,hFact,hFfocus⟩ := R.exists_focusData h00 hc hs hsmall hA hD htag
      obtain ⟨E,hcoord,hact,hfocus,hProtected⟩ := F.exists_protected_family_step h00 hc linear hκ hs hv V
        hsmall hΓ hV hVS hSV hnt C hCA hC
      have hact' : E.activeTags = R.activeTags := hact.trans hFact
      have hfocus' (x u) : E.focus x u = Barycentre.mean (R.fibre u) := (hfocus x u).trans (hFfocus u)
      let E' (i : Fin k) : CentripetalData (G := G) (C i) := (hProtected i).choose
      have hE' (i) : ∀ p ∈ (C i).carrier, (E' i).point p = E.point p := (hProtected i).choose_spec
      let A₀ := (regularizeMap E.map.image).image
      let C₀ (i : Fin k) := (regularizeMap (E' i).map.image).image
      let f₀ := stepMap E
      let g₀ (i : Fin k) := stepMap (E' i)
      have hstep : SpecialCovariantChain (G := G) A A₀ f₀ := stepMap_chain E h00 hc hκ hs hv
      have hg₀ (i) : SpecialCovariantChain (G := G) (C i) (C₀ i) (g₀ i) := stepMap_chain (E' i) h00 hc hκ hs hv
      have hpoint₀ (i) (p : C i) : (g₀ i p).val = (f₀ ⟨p.val,hCA i p.property⟩).val :=
        congrArg regularize (hE' i p.val p.property)
      have hC₀A₀ (i) : (C₀ i).carrier ⊆ A₀.carrier :=
        target_subset_of_liesOver f₀ (g₀ i) ((hg₀ i).bijective h00).surjective (hCA i) (hpoint₀ i)
      have hA₀ : ProperInvariant S A₀.carrier := regularization_properInvariant h00 hc hκ hs hv _
        (E.image_properInvariant h00 hc hκ hs hv) E.image_vfDoublyBounded
      have hA₀D : VFDoublyBounded A₀.carrier := regularized_vfDoublyBounded E.image_vfDoublyBounded
      have htag₀ : ∀ p ∈ A₀.carrier, ∀ q ∈ A₀.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
        rw [show A₀.carrier = regularize '' E.map.image.carrier from regularization_carrier _]
        exact regularized_tagged _
      have hC₀ (i) : ProperInvariant S (C₀ i).carrier := regularization_properInvariant h00 hc hκ hs hv _
        ((E' i).image_properInvariant h00 hc hκ hs hv) (E' i).image_vfDoublyBounded
      let Q := R.stepFamily E h00 hcoord hact' hfocus'
      obtain ⟨s,B,f,hP,hchain,hB,hBD,hPieces⟩ := ih A₀ Q hA₀ hA₀D htag₀
        (R.stepFamily_bound E h00 hcoord hact' hfocus' N hb) C₀ hC₀A₀ hC₀
      refine ⟨s,B,f.comp f₀,.step R E h00 hcoord hact' hfocus' hP,.comp hstep hchain,hB,hBD,fun i => ?_⟩
      obtain ⟨D,g,hg,hpoint⟩ := hPieces i
      refine ⟨D,g.comp (g₀ i),.comp (hg₀ i) hg,fun p => ?_⟩
      change (g (g₀ i p)).val = (f (f₀ ⟨p.val,hCA i p.property⟩)).val
      rw [hpoint]
      have he : (⟨(g₀ i p).val,hC₀A₀ i (g₀ i p).property⟩ : A₀) = f₀ ⟨p.val,hCA i p.property⟩ :=
        Subtype.ext (hpoint₀ i p)
      rw [he]

/-- A terminating protected unary root process. Each restriction is the
literal restriction of the ambient map to its actual definable image. -/
theorem exists_protected_process {r : ℕ}
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} (R : UnaryRootFamily A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ f : Map A B,
      UnaryRootProcess (G := G) A R B f ∧ SpecialCovariantChain (G := G) A B f ∧
      ProperInvariant S B.carrier ∧ VFDoublyBounded B.carrier ∧
      (IsRVPullback A.carrier → IsRVPullback B.carrier) ∧
      ∀ i, SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage := by
  obtain ⟨N,hN⟩ := R.exists_uniform_bound hc hs hsmall
  have hb (u) : (R.fibre u).card ≤ N := by simpa only [R.rawFamily_labels] using hN (rvValues u)
  obtain ⟨s,B,f,hP,hchain,hB,hBD,hPieces⟩ := exists_protected_process_of_bound h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt N A R hA hD htag hb C hCA hC
  refine ⟨s,B,f,hP,hchain,hB,hBD,hP.rvPullback,fun i => ?_⟩
  obtain ⟨D,g,hg,hpoint⟩ := hPieces i
  exact hg.restriction_of_liesOver h00 f (hCA i) hpoint

end UnaryRootFamily
end DiamondIntegral.Section6
