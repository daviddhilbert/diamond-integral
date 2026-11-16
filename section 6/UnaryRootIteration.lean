import «section 6».UnaryRootStep

/-! Termination of the actual finite-aperture unary root construction.
Every step is a permitted centripetal map followed by regularization;
remaining roots occur only on noncore labels. This is the construction
loop, before the transported partition-preparation invariant is added. -/

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

inductive UnaryRootProcess : {r s : ℕ} →
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) → UnaryRootFamily A →
    (B : DefSet (rawMixedSpace (M := M) 1 s) S) → Map A B → Prop where
  | done (A : DefSet (rawMixedSpace (M := M) 1 r) S) (R : UnaryRootFamily A)
      (hA : ProperInvariant S A.carrier) (hR : R.roots.carrier = ∅) : UnaryRootProcess A R A (Map.id A)
  | step {A : DefSet (rawMixedSpace (M := M) 1 r) S} (R : UnaryRootFamily A)
      (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
      (hcoord : D.coordinate = 0) (hact : D.activeTags = R.activeTags)
      (hfocus : ∀ x u, D.focus x u = Barycentre.mean (R.fibre u))
      {B : DefSet (rawMixedSpace (M := M) 1 s) S}
      {f : Map (regularizeMap D.map.image).image B}
      (tail : UnaryRootProcess (regularizeMap D.map.image).image
        (R.stepFamily D h00 hcoord hact hfocus) B f) :
      UnaryRootProcess A R B (f.comp (UnaryRootFamily.stepMap D))

namespace UnaryRootProcess

variable {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) S} {R : UnaryRootFamily A}
variable {B : DefSet (rawMixedSpace (M := M) 1 s) S} {f : Map A B}

theorem specialChain (P : UnaryRootProcess (G := G) A R B f)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    SpecialCovariantChain (G := G) A B f := by
  induction P with
  | done A R hA hR => exact .identity A hA
  | step R D h00' hcoord hact hfocus tail ih =>
      exact .comp (UnaryRootFamily.stepMap_chain D h00 hc hκ hs hv) ih

end UnaryRootProcess

namespace UnaryRootFamily

variable {r : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem roots_empty_of_bound_zero (R : UnaryRootFamily A)
    (hbound : ∀ u, (R.fibre u).card ≤ 0) : R.roots.carrier = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hx : p.1 0 ∈ R.fibre p.2 := by
    rw [R.mem_fibre]
    have hEta : (fun _ : Fin 1 => p.1 0) = p.1 := by funext i; fin_cases i; rfl
    rw [hEta]
    exact hp
  have hpos := Finset.card_pos.mpr ⟨_,hx⟩
  have hb := hbound p.2
  omega

theorem exists_process_of_bound
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
      ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ f : Map A B,
        UnaryRootProcess (G := G) A R B f ∧ ProperInvariant S B.carrier ∧ VFDoublyBounded B.carrier ∧
          ∀ p ∈ B.carrier, ∀ q ∈ B.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  induction N with
  | zero =>
      intro r A R hA hD htag hb
      exact ⟨r,A,Map.id A,.done A R hA (R.roots_empty_of_bound_zero hb),hA,hD,htag⟩
  | succ N ih =>
      intro r A R hA hD htag hb
      obtain ⟨F,hFact,hFfocus⟩ := R.exists_focusData h00 hc hs hsmall hA hD htag
      obtain ⟨D,hcoord,hact,hfocus,hmap⟩ := F.exists_centripetal_data h00 hc linear hκ hs hv V hsmall
        hΓ hV hVS hSV hnt
      have hact' : D.activeTags = R.activeTags := hact.trans hFact
      have hfocus' (x u) : D.focus x u = Barycentre.mean (R.fibre u) :=
        (hfocus x u).trans (hFfocus u)
      let C := (regularizeMap D.map.image).image
      let Q := R.stepFamily D h00 hcoord hact' hfocus'
      have hC : ProperInvariant S C.carrier := regularization_properInvariant h00 hc hκ hs hv _
        (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded
      have hCD : VFDoublyBounded C.carrier := by
        obtain ⟨γ,hγ⟩ := D.image_vfDoublyBounded
        refine ⟨γ,?_⟩
        rw [regularization_carrier]
        rintro _ ⟨p,hp,rfl⟩ i
        exact hγ p hp i
      have htagC : ∀ p ∈ C.carrier, ∀ q ∈ C.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
        rw [show C.carrier = regularize '' D.map.image.carrier from regularization_carrier _]
        exact regularized_tagged _
      obtain ⟨s,B,g,hP,hB,hBD,htagB⟩ := ih C Q hC hCD htagC
        (R.stepFamily_bound D h00 hcoord hact' hfocus' N hb)
      exact ⟨s,B,g.comp (stepMap D),.step R D h00 hcoord hact' hfocus' hP,hB,hBD,htagB⟩

theorem exists_process (R : UnaryRootFamily A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ f : Map A B,
      UnaryRootProcess (G := G) A R B f ∧ SpecialCovariantChain (G := G) A B f ∧
        ProperInvariant S B.carrier ∧ VFDoublyBounded B.carrier := by
  obtain ⟨N,hN⟩ := R.exists_uniform_bound hc hs hsmall
  have hb (u) : (R.fibre u).card ≤ N := by simpa only [R.rawFamily_labels] using hN (rvValues u)
  obtain ⟨s,B,f,hP,hB,hBD,htagB⟩ := exists_process_of_bound h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt N A R hA hD htag hb
  exact ⟨s,B,f,hP,hP.specialChain h00 hc hκ hs hv,hB,hBD⟩

end UnaryRootFamily
end DiamondIntegral.Section6
