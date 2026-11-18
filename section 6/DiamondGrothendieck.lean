import «section 6».DiamondProduct
import «section 6».GammaConstantMaps
import «section 6».FiniteInvariantRadii
import «section 3».Grothendieck
import Section4.RVRestrictions

/-! The Grothendieck semigroup `K_+ μVF^◇[n]` (Definition 3.1 instantiated with
Definition 6.34).

The empty object, the restriction of an object to a definable proper invariant
subset, and the positive scissor presentation: isomorphism is `Isomorphic`
(finite chains of relatively unary steps), and a scissor splits an object into
a proper invariant piece and its complement, as in Section 3's measured VF
presentation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.DiamondGrothendieck
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
theorem properInvariant_empty (hc : CanonicalStructure.IsCanonical (M := M)) {r : ℕ} : ProperInvariant S (∅ : Set (Mixed M n r)) :=
  ⟨(rawMixedSpace (M := M) n r).definable_empty S, ⟨1, fun _ h => False.elim h⟩,
    ⟨1, fun _ h => False.elim h⟩,
    fun _ => ⟨fun _ => 1, fun _ => (gamma_one_named (S := S) hc).mono Set.subset_union_left,
      fun _ _ _ => ⟨fun h => False.elim h, fun h => False.elim h⟩⟩⟩

variable (hc : CanonicalStructure.IsCanonical (M := M))

/-- The empty object of `μVF^◇[n]`. -/
def emptyObject (n : ℕ) : VFObject (M := M) S n where
  labels := 0
  carrier := DefSet.empty (rawMixedSpace (M := M) n 0) S
  form := gammaOneMap hc _
  proper := properInvariant_empty hc
  formCovariant _ := ⟨fun _ => 1, fun _ => (gamma_one_named (S := S) hc).mono Set.subset_union_left,
    fun _ _ hx _ _ => False.elim hx⟩
  finiteRV _ := Set.finite_empty.subset (fun _ h => False.elim h)

/-- The restriction of an object to a definable proper invariant subset. -/
def restrictObject (A : VFObject (M := M) S n) (X : DefSet (rawMixedSpace (M := M) n A.labels) S)
    (hX : X.carrier ⊆ A.carrier.carrier) (hP : ProperInvariant S X.carrier) :
    VFObject (M := M) S n where
  labels := A.labels
  carrier := X
  form := A.form.restrict hX
  proper := hP
  formCovariant t := by
    obtain ⟨α, hα, hcov⟩ := A.formCovariant t
    exact ⟨α, hα, fun x y hx hy hxy => hcov x y (hX hx) (hX hy) hxy⟩
  finiteRV x := (A.finiteRV x).subset (fun _ h => hX h)

/-- The complementary piece. -/
def complObject (A : VFObject (M := M) S n)
    (X : DefSet (rawMixedSpace (M := M) n A.labels) S) (hP : ProperInvariant S X.carrier) :
    VFObject (M := M) S n :=
  restrictObject A (A.carrier.sdiff X) (fun _ h => h.1) (A.proper.diff hP)

/-- A scissor: an object, a proper invariant piece, its complement and the
empty object. -/
def Scissor (A B D E : VFObject (M := M) S n) : Prop :=
  ∃ U : VFObject (M := M) S n, ∃ X : DefSet (rawMixedSpace (M := M) n U.labels) S,
    ∃ hX : X.carrier ⊆ U.carrier.carrier, ∃ hP : ProperInvariant S X.carrier,
      A = restrictObject U X hX hP ∧ B = complObject U X hP ∧ D = U ∧ E = emptyObject hc n

variable (G) in
/-- The positive scissor presentation of `μVF^◇[n]`. -/
def presentation (n : ℕ) : DiamondIntegral.Section3.ScissorPresentation (VFObject (M := M) S n) where
  iso A B := Isomorphic G A B
  empty := emptyObject hc n
  scissor := Scissor hc

variable (G S) in
/-- The Grothendieck semigroup `K_+ μVF^◇[n]`. -/
abbrev KPlus (n : ℕ) := DiamondIntegral.Section3.KPlus (presentation (S := S) G hc n)

variable (G S) in
/-- The Grothendieck group `K μVF^◇[n]`. -/
abbrev KGroup (n : ℕ) := DiamondIntegral.Section3.KGroup (presentation (S := S) G hc n)

variable (G) in
/-- The class of an object in `K_+ μVF^◇[n]`. -/
def vfClass (A : VFObject (M := M) S n) : KPlus S G hc n :=
  DiamondIntegral.Section3.positiveClass (presentation G hc n) A

theorem vfClass_iso {A B : VFObject (M := M) S n} (h : Isomorphic G A B) :
    vfClass G hc A = vfClass G hc B :=
  DiamondIntegral.Section3.positiveClass_iso (presentation G hc n) h

@[simp] theorem vfClass_empty : vfClass G hc (emptyObject (S := S) hc n) = 0 :=
  DiamondIntegral.Section3.positiveClass_empty (presentation G hc n)

theorem vfClass_scissor (U : VFObject (M := M) S n) (X : DefSet (rawMixedSpace (M := M) n U.labels) S)
    (hX : X.carrier ⊆ U.carrier.carrier) (hP : ProperInvariant S X.carrier) :
    vfClass G hc (restrictObject U X hX hP) + vfClass G hc (complObject U X hP) = vfClass G hc U := by
  have h := DiamondIntegral.Section3.positiveClass_scissor (presentation G hc n)
    (a := restrictObject U X hX hP) (b := complObject U X hP) (c := U) (d := emptyObject hc n)
    ⟨U, X, hX, hP, rfl, rfl, rfl, rfl⟩
  change vfClass G hc _ + vfClass G hc _ = vfClass G hc _ + vfClass G hc _ at h
  rw [h, vfClass_empty, add_zero]

end DiamondIntegral.Section6.DiamondGrothendieck
