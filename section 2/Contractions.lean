import «section 2».RVHull
import Section5.Core

/-! Definition 2.40: descent along a coordinate map, specialized to RV
coordinates with all existing labels retained. The generic formulation
also gives the stated residue and valuation versions by substituting their
coordinate maps on their natural domains. -/

set_option backward.isDefEq.respectTransparency false

namespace DiamondIntegral.Section2

def IsContractibleAlong {A B Q R : Type} (q : A → Q) (r : B → R) (f : A → B) : Prop :=
  ∀ a b, q a = q b → r (f a) = r (f b)

noncomputable def contractionAlong {A B Q R : Type} (q : A → Q) (r : B → R) (f : A → B) :
    Set.range q → Set.range r :=
  fun u => ⟨r (f u.property.choose),f u.property.choose,rfl⟩

theorem contractionAlong_spec {A B Q R : Type} (q : A → Q) (r : B → R) (f : A → B)
    (hf : IsContractibleAlong q r f) (a : A) :
    (contractionAlong q r f ⟨q a,a,rfl⟩).val = r (f a) :=
  hf _ a (Set.mem_range.mpr ⟨a,rfl⟩).choose_spec

theorem contractionAlong_unique {A B Q R : Type} (q : A → Q) (r : B → R) (f : A → B)
    (hf : IsContractibleAlong q r f) (g : Set.range q → Set.range r)
    (hg : ∀ a : A, (g ⟨q a,a,rfl⟩).val = r (f a)) : g = contractionAlong q r f := by
  funext u
  obtain ⟨a,ha⟩ := u.property
  have hu : u = ⟨q a,a,rfl⟩ := Subtype.ext ha.symm
  rw [hu]
  apply Subtype.ext
  exact (hg a).trans (contractionAlong_spec q r f hf a).symm

theorem isContractibleAlong_iff_exists {A B Q R : Type} (q : A → Q) (r : B → R) (f : A → B) :
    IsContractibleAlong q r f ↔
      ∃ g : Set.range q → Set.range r, ∀ a : A, (g ⟨q a,a,rfl⟩).val = r (f a) := by
  constructor
  · intro hf
    exact ⟨contractionAlong q r f,contractionAlong_spec q r f hf⟩
  · rintro ⟨g,hg⟩ a b hab
    have he : (⟨q a,a,rfl⟩ : Set.range q) = ⟨q b,b,rfl⟩ := Subtype.ext hab
    exact (hg a).symm.trans ((congrArg (fun u => (g u).val) he).trans (hg b))

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m k l : ℕ}

def IsRVContractible {A : Set (Mixed M n m)} {B : Set (Mixed M k l)} (f : A → B) : Prop :=
  IsContractibleAlong (fun a : A => rvCoordinates M a.val) (fun b : B => rvCoordinates M b.val) f

noncomputable def rvContraction {A : Set (Mixed M n m)} {B : Set (Mixed M k l)} (f : A → B) :=
  contractionAlong (fun a : A => rvCoordinates M a.val) (fun b : B => rvCoordinates M b.val) f

theorem rvCoordinates_eq_companion_key (x : Mixed M n m) :
    rvCoordinates M x = SpecialTransformations.Section5.key x := rfl

theorem isRVContractible_iff_companion {S : Set M}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
    {B : SpecialTransformations.Section5.DefSet (M := M) S k l} (f : A → B) :
    IsRVContractible f ↔ SpecialTransformations.Section5.Contractible f := Iff.rfl

noncomputable def definableRVContraction {S : Set M}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
    {B : SpecialTransformations.Section5.DefSet (M := M) S k l}
    (f : SpecialTransformations.Section5.Map A B) (hf : IsRVContractible f) :
    SpecialTransformations.Section5.Map (SpecialTransformations.Section5.keyImage A)
      (SpecialTransformations.Section5.keyImage B) :=
  SpecialTransformations.Section5.contractionMap f ((isRVContractible_iff_companion f).mp hf)

end DiamondIntegral.Section2
