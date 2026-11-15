import IntegrationSection5.UniformRelativeTrace

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
variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

namespace UniformRelativeTrace

def flagCount {m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} : UniformRelativeTrace S n A B → ℕ
  | .nil _ => 0
  | .canonical _ tail => tail.flagCount
  | .focus _ tail => 1+tail.flagCount

def flagMap {m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (T : UniformRelativeTrace S n A B) : Map A (PresentedSet.univ (pointSpace 0 T.flagCount) S) :=
  match T with
  | .nil A => constantRVMap A 0
  | .canonical i tail => Map.comp tail.flagMap (coordinateCanonicalBijection A i)
  | .focus D tail => pairRVMaps (membershipMap A (PresentedSet.mk D.locus D.locus_definable))
      (Map.comp tail.flagMap D.toImage)

theorem focus_flag_nonzero {i : Fin n} {k : Fin m} (D : FibreFocusData A i k)
    (T : UniformRelativeTrace S n D.image B) (a : A) :
    ((UniformRelativeTrace.focus D T).flagMap a).val.2 (0 : Fin (1+T.flagCount)) ≠ rv (0 : VF (M := M)) ↔ a.val ∈ D.locus := by
  change (if a.val ∈ D.locus then rv (1 : VF (M := M)) else rv (0 : VF (M := M))) ≠ rv 0 ↔ _
  by_cases ha : a.val ∈ D.locus
  · simp [ha,Ne.symm (rv_zero_ne_one (M := M))]
  · simp [ha]

end UniformRelativeTrace
end IntegrationInACVF.Section5
