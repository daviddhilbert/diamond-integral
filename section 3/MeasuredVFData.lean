import «section 3».MeasuredVFScissors

/-! A uniform data presentation of the measured VF objects in every
degree. It is equivalent to the separate zero and positive definitions;
all morphisms still use those original groupoids. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure MeasuredVFData (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M)) (k : ℕ) where
  arity : ℕ
  domain : DefSet (rawMixedSpace (M := M) k arity) (C.base : Set M)
  finite : ∀ a, {t | (a, t) ∈ domain.carrier}.Finite
  form : GammaVolumeForm hc domain

variable {C : BaseContext M} {hc : CanonicalStructure.IsCanonical (M := M)}

def MeasuredVFData.toObject : {k : ℕ} → MeasuredVFData C hc k → MeasuredVFObject C hc k
  | 0, A => ⟨A.arity, A.domain, A.finite, A.form⟩
  | _ + 1, A => ⟨A.arity, A.domain, A.finite, A.form⟩

def MeasuredVFData.ofObject : {k : ℕ} → MeasuredVFObject C hc k → MeasuredVFData C hc k
  | 0, A => ⟨A.arity, A.domain, A.finite, A.form⟩
  | _ + 1, A => ⟨A.arity, A.domain, A.finite, A.form⟩

@[simp] theorem MeasuredVFData.of_toObject {k : ℕ} (A : MeasuredVFData C hc k) :
    MeasuredVFData.ofObject A.toObject = A := by cases k <;> rfl

@[simp] theorem MeasuredVFData.to_ofObject {k : ℕ} (A : MeasuredVFObject C hc k) :
    (MeasuredVFData.ofObject A).toObject = A := by cases k <;> rfl

def measuredVFDataEquiv (k : ℕ) : MeasuredVFData C hc k ≃ MeasuredVFObject C hc k where
  toFun := MeasuredVFData.toObject
  invFun := MeasuredVFData.ofObject
  left_inv := MeasuredVFData.of_toObject
  right_inv := MeasuredVFData.to_ofObject

def MeasuredVFData.empty (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M)) (k : ℕ) :
    MeasuredVFData C hc k where
  arity := 0
  domain := DefSet.empty (rawMixedSpace k 0) (C.base : Set M)
  finite _ := Set.finite_empty
  form := Map.empty (rawMixedSpace k 0) (volumeGammaSpace hc) (C.base : Set M)

def MeasuredVFData.restrict {k : ℕ} (A : MeasuredVFData C hc k)
    (X : DefSet (rawMixedSpace (M := M) k A.arity) (C.base : Set M))
    (hX : X.carrier ⊆ A.domain.carrier) : MeasuredVFData C hc k where
  arity := A.arity
  domain := X
  finite a := (A.finite a).subset (fun _ h => hX h)
  form := A.form.comp (Map.inclusion hX)

end DiamondIntegral.Section3
