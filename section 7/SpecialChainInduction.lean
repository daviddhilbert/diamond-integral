import «section 7».SpecialChainRel
import «section 6».ScalarApertureInclusion
import «section 6».UnaryApertureInclusion

/-! Lemma 7.11 (`special:to:blowup:coa`) for chains.

Along a special covariant chain or a relative aperture chain, a chain set and
its transported form give a chain set at the end, whose class is reached from
the class of the start by blowups (`relative_chain`, `unary_chain`):
* identity, regularization and zero-centred steps keep the class
  (`clsG_reg`, `clsG_zc`);
* centripetal and relative steps are blowups of length one (`step_rel`; an
  original centripetal step is relative data with the same point map,
  `CentripetalData.relativeData`, and so is a unary relative step,
  `UnaryRelativeApertureData.exists_relativeData`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.SpecialChainInduction
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.SpecialChains DiamondIntegral.Section7.SpecialChainRel
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.ElementaryBlowups
open IntegrationInACVF.Section6.Iteration

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {r : ℕ}

/-! ### Transport of chain sets along equalities -/

section Transport
variable {T : LRV.Substructure M} {n : ℕ} {X X' : DefSet (rawMixedSpace (M := M) n r) (T : Set M)}

/-- A chain set transported along an equality of sets. -/
def transport (h : X = X') (g : Good T X) : Good T X' := h ▸ g

theorem transport_form (h : X = X') (g : Good T X) (p : X) :
    (transport h g).form ⟨p.val, h ▸ p.property⟩ = g.form p := by
  subst h
  rfl

theorem clsG_transport (hc : CanonicalStructure.IsCanonical (M := M)) (h : X = X') (g : Good T X) :
    clsG hc (transport h g) = clsG hc g := by
  subst h
  rfl

end Transport

/-! ### Induction along chains -/

section Induction
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {k : ℕ}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk (T : Set M) < κ)
variable (h00 : M ⊨ Axioms.ACVF00)

/-- The conclusion of Lemma 7.11 along a map `f : A → B`: every chain set
structure on `A` transports to one on `B` whose class is a blowup of the class
on `A`. -/
def Claim {s : ℕ} (A : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M))
    (B : DefSet (rawMixedSpace (M := M) (1 + k) s) (T : Set M)) (f : Map A B) : Prop :=
  ∀ g : Good T A, ∃ g' : Good T B, (∀ p : A, g'.form (f p) = g.form p) ∧
    ∃ m, BlowupSteps m (clsG hc g) (clsG hc g')

theorem claim_comp {s t : ℕ} {A : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) (1 + k) s) (T : Set M)}
    {C : DefSet (rawMixedSpace (M := M) (1 + k) t) (T : Set M)} {f : Map A B} {g : Map B C}
    (hf : Claim hc A B f) (hg : Claim hc B C g) : Claim hc A C (g.comp f) := by
  intro g0
  obtain ⟨g1, hf1, m1, hs1⟩ := hf g0
  obtain ⟨g2, hf2, m2, hs2⟩ := hg g1
  exact ⟨g2, fun p => (hf2 (f p)).trans (hf1 p), m1 + m2, hs1.trans hs2⟩

/-- A relative step. -/
theorem claim_relative {A : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M)}
    (D : DiamondIntegral.Section6.RelativeApertureData (G := G) A) :
    Claim hc A D.map.image D.bijection := by
  intro g
  exact ⟨imageGood hc g D hκ hs hsmall h00, fun p => imageGood_form hc g D hκ hs hsmall h00 p, 1,
    Steps.single (step_rel hc g D hκ hs hsmall h00)⟩

/-- A step given by relative data with the same point map. -/
theorem claim_of_point {s : ℕ} {A : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) (1 + k) s) (T : Set M)} (f : Map A B) (hs1 : s = 1 + r)
    (D : DiamondIntegral.Section6.RelativeApertureData (G := G) A)
    (hB : B.carrier = hs1 ▸ D.map.image.carrier) (hf : ∀ p : A, (f p).val = hs1 ▸ D.point p.val) :
    Claim hc A B f := by
  subst hs1
  have hE : D.map.image = B := DefSet.eq_of_carrier_eq hB.symm
  intro g
  refine ⟨transport hE (imageGood hc g D hκ hs hsmall h00), fun p => ?_, 1, ?_⟩
  · have hp : f p = ⟨(D.bijection p).val, hE ▸ (D.bijection p).property⟩ := Subtype.ext (hf p)
    rw [hp, transport_form, imageGood_form]
  · rw [clsG_transport]
    exact Steps.single (step_rel hc g D hκ hs hsmall h00)

/-- Special covariant chains. -/
theorem special_chain {s : ℕ} {A : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) (1 + k) s) (T : Set M)} {f : Map A B}
    (h : SpecialCovariantChain (G := G) A B f) : Claim hc A B f := by
  induction h with
  | identity A _ =>
    intro g
    exact ⟨g, fun _ => rfl, 0, .refl _⟩
  | regularize A _ _ =>
    intro g
    refine ⟨regGood g, fun p => regForm_apply g p, 0, ?_⟩
    rw [clsG_reg]
    exact .refl _
  | centripetal A D =>
    exact claim_of_point hc hκ hs hsmall h00 D.bijection rfl D.relativeData
      (by rw [RelativeApertureData.image_carrier, CentripetalData.image_carrier]
          ext q
          constructor
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, hp, (D.relativeData_point ⟨p, hp⟩).symm⟩
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, hp, D.relativeData_point ⟨p, hp⟩⟩)
      (fun p => (D.relativeData_point p).symm)
  | zeroCentered A D =>
    intro g
    refine ⟨zcGood g D h00, fun p => zcGood_form g D h00 p, 0, ?_⟩
    rw [clsG_zc]
    exact .refl _
  | comp _ _ ihf ihg => exact claim_comp hc ihf ihg

/-- Lemma 7.11 along relative aperture chains. -/
theorem relative_chain {s : ℕ} {A : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) (1 + k) s) (T : Set M)} {f : Map A B}
    (h : RelativeApertureChain (G := G) A B f) : Claim hc A B f := by
  induction h with
  | original h => exact special_chain hc hκ hs hsmall h00 h
  | relative A D => exact claim_relative hc hκ hs hsmall h00 D
  | comp _ _ ihf ihg => exact claim_comp hc ihf ihg

end Induction

end DiamondIntegral.Section7.SpecialChainInduction
