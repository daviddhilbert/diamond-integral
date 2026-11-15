import IntegrationSection5.FibreFocusMaps

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

inductive UniformRelativeTrace (S : Set M) (n : ℕ) : {m l : ℕ} →
    DefSet (M := M) S n m → DefSet (M := M) S n l → Type where
  | nil {m} (A : DefSet (M := M) S n m) : UniformRelativeTrace S n A A
  | canonical {m l} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
      (i : Fin n) (tail : UniformRelativeTrace S n (coordinateCanonicalImage A i) B) : UniformRelativeTrace S n A B
  | focus {m l} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
      {i : Fin n} {k : Fin m} (D : FibreFocusData A i k)
      (tail : UniformRelativeTrace S n D.image B) : UniformRelativeTrace S n A B

namespace UniformRelativeTrace
variable {S : Set M} {n m l r : ℕ} {A : DefSet (M := M) S n m}
  {B : DefSet (M := M) S n l} {C : DefSet (M := M) S n r}

def toMap {m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} :
    UniformRelativeTrace S n A B → Map A B
  | .nil A => Map.id A
  | .canonical i tail => Map.comp tail.toMap (coordinateCanonicalBijection _ i)
  | .focus D tail => Map.comp tail.toMap D.toImage

theorem bijective (T : UniformRelativeTrace S n A B) : Function.Bijective T.toMap := by
  induction T with
  | nil A => exact Function.bijective_id
  | canonical i tail ih => exact ih.comp (coordinateCanonicalBijection_bijective _ i)
  | focus D tail ih => exact ih.comp D.toImage_bijective

def append {m l r : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    {C : DefSet (M := M) S n r} (T : UniformRelativeTrace S n A B) (U : UniformRelativeTrace S n B C) : UniformRelativeTrace S n A C :=
  match T with
  | .nil _ => U
  | .canonical i tail => .canonical i (tail.append U)
  | .focus D tail => .focus D (tail.append U)

theorem append_apply (T : UniformRelativeTrace S n A B) (U : UniformRelativeTrace S n B C) (a : A) :
    (T.append U).toMap a = U.toMap (T.toMap a) := by
  induction T with
  | nil A => rfl
  | canonical i tail ih => exact ih U _
  | focus D tail ih => exact ih U _

end UniformRelativeTrace
end IntegrationInACVF.Section5
