import «section 6».BranchedShearCommonFreezing
import «section 6».CarriedDefinableMaps

/-! An actual definable zero section restricts a full scalar family to
inactive coordinates. Its complete graph stays over the original base,
and full continuity restricts along the continuous zero section. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r m : ℕ}

def vfTupleZerosMap {P : SpecialTransformations.DefinableGeometry.Space LRV M} (A : DefSet P S) :
    Map A (DefSet.univ (rawVFSpace (M := M) m) S) := by
  let F (_ : P.Index → M) : Fin m → M := fun _ => iVFZero
  have hF : S.DefinableMap LRV F := fun _ => rawVFZero_constant_definable
  refine Map.ofCodes A (fun _ => fun _ => (0 : VF M)) F hF
    (fun _ => ⟨fun _ => 0,rfl⟩) ?_
  intro c
  apply vfValues_injective
  exact vfValues_decode _

def mixedSnocZeroMap (S : Set M) (n r : ℕ) :
    Map (DefSet.univ (rawMixedSpace (M := M) n r) S) (DefSet.univ (rawMixedSpace (M := M) (n+1) r) S) :=
  appendTailMap (Map.id _) (vfTupleZerosMap (m := 1) _)

theorem mixedSnocZeroMap_value (S : Set M) (n r : ℕ)
    (p : DefSet.univ (rawMixedSpace (M := M) n r) S) :
    (mixedSnocZeroMap S n r p).val=(Fin.snoc p.val.1 0,p.val.2) := by
  change (productTuple p.val.1 (fun _ : Fin 1 => (0 : VF M)),p.val.2)=_
  rw [productTuple_singleton_eq_snoc]

def inactiveScalarRestriction
    (f : Map (DefSet.univ (rawMixedSpace (M := M) (n+1) r) S) (DefSet.univ (rawVFSpace 1) S)) :
    Map (DefSet.univ (rawMixedSpace (M := M) n r) S) (DefSet.univ (rawVFSpace 1) S) :=
  f.comp (mixedSnocZeroMap S n r)

theorem inactiveScalarRestriction_value
    (f : Map (DefSet.univ (rawMixedSpace (M := M) (n+1) r) S) (DefSet.univ (rawVFSpace 1) S))
    (u : Fin r → RVInfinity M) (x : Fin n → VF M) :
    totalFocusFibre (inactiveScalarRestriction f) u x=totalFocusFibre f u (Fin.snoc x 0) := by
  rw [totalFocusFibre_at _ u x (Set.mem_univ _),totalFocusFibre_at _ u (Fin.snoc x 0) (Set.mem_univ _)]
  apply congrArg (fun p => (f p).val)
  apply Subtype.ext
  exact mixedSnocZeroMap_value S n r ⟨(x,u),Set.mem_univ _⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem inactiveScalarRestriction_continuous
    (f : Map (DefSet.univ (rawMixedSpace (M := M) (n+1) r) S) (DefSet.univ (rawVFSpace 1) S))
    (u : Fin r → RVInfinity M) (hf : Continuous (totalFocusFibre f u)) :
    Continuous (totalFocusFibre (inactiveScalarRestriction f) u) := by
  have he : totalFocusFibre (inactiveScalarRestriction f) u=fun x => totalFocusFibre f u (Fin.snoc x 0) :=
    funext (inactiveScalarRestriction_value f u)
  rw [he]
  apply hf.comp
  apply continuous_pi
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [Fin.snoc_last] using (continuous_const : Continuous (fun _ : Fin n → VF M => (0 : VF M)))
  · simpa only [Fin.snoc_castSucc] using (continuous_apply i : Continuous (fun x : Fin n → VF M => x i))

end DiamondIntegral.Section6
