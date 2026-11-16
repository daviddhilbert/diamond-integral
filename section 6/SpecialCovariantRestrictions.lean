import «section 6».ProtectedUnaryFoci
import «section 6».UnaryRootStep

/-! Pointwise compatible special chains give the literal restriction to
its actual image. This identifies the protected unary constructors with
those restrictions, including their full original-base graphs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem defSet_eq_of_carrier_eq {P : Space LRV M} {A B : DefSet P S}
    (h : A.carrier = B.carrier) : A = B := by
  cases A
  cases B
  cases h
  rfl

theorem SpecialCovariantChain.changeTarget
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B C : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {g : Map A C}
    (hBC : B = C) (hpoint : ∀ p : A, (f p).val = (g p).val)
    (hf : SpecialCovariantChain (G := G) A B f) : SpecialCovariantChain (G := G) A C g := by
  subst C
  have he : f = g := Map.ext (fun p => Subtype.ext (hpoint p))
  simpa only [he] using hf

theorem SpecialCovariantChain.restriction_of_liesOver
    {A C : DefSet (rawMixedSpace (M := M) n r) S}
    {B D : DefSet (rawMixedSpace (M := M) n s) S}
    (h00 : M ⊨ Axioms.ACVF00) (f : Map A B) {g : Map C D}
    (hg : SpecialCovariantChain (G := G) C D g) (hCA : C.carrier ⊆ A.carrier)
    (hpoint : ∀ p : C, (g p).val = (f ⟨p.val,hCA p.property⟩).val) :
    SpecialCovariantChain (G := G) C (f.restrict hCA).image (f.restrict hCA).toImage := by
  have hTarget : D = (f.restrict hCA).image := by
    apply defSet_eq_of_carrier_eq
    ext q
    constructor
    · intro hq
      obtain ⟨p,hp⟩ := (hg.bijective h00).surjective ⟨q,hq⟩
      exact ⟨p,(hpoint p).symm.trans (congrArg Subtype.val hp)⟩
    · rintro ⟨p,hp⟩
      have he : (g p).val = q := (hpoint p).trans hp
      exact he ▸ (g p).property
  exact hg.changeTarget hTarget hpoint

theorem centripetal_restriction_chain
    {A C : DefSet (rawMixedSpace (M := M) n r) S}
    (h00 : M ⊨ Axioms.ACVF00) (D : CentripetalData (G := G) A) (E : CentripetalData (G := G) C)
    (hCA : C.carrier ⊆ A.carrier) (hpoint : ∀ p ∈ C.carrier, E.point p = D.point p) :
    SpecialCovariantChain (G := G) C (D.bijection.restrict hCA).image (D.bijection.restrict hCA).toImage :=
  (SpecialCovariantChain.centripetal C E).restriction_of_liesOver h00 D.bijection hCA
    (fun p => hpoint p.val p.property)

theorem regularization_restriction_chain
    {A C : DefSet (rawMixedSpace (M := M) n r) S}
    (h00 : M ⊨ Axioms.ACVF00) (hCA : C.carrier ⊆ A.carrier)
    (hC : ProperInvariant S C.carrier) (hD : VFDoublyBounded C.carrier) :
    SpecialCovariantChain (G := G) C ((regularization A).restrict hCA).image
      ((regularization A).restrict hCA).toImage :=
  (SpecialCovariantChain.regularize C hC hD).restriction_of_liesOver h00 (regularization A) hCA (fun _ => rfl)

end DiamondIntegral.Section6
