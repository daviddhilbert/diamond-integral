import «section 6».MeasuredRVHeads
import Section9.DerivativeCoordinates

/-! Full total derivatives of scalar coefficient maps on mixed domains.
An actual coordinate padding embeds a scalar map into a same-arity mixed
map, and projection of its derivative recovers the scalar derivative. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def mixedScalarPadMap {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (i : Fin n) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n r) S) := by
  let F (k : Fin n) := if k = i then f else (vfTupleSelectMap S (fun _ : Fin 1 => k)).comp (mixedVFHeadMap A)
  exact ((vfTupleAssembleMap A n F).pair (rvTailMap A)).toUniv

theorem mixedScalarPadMap_value {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (i : Fin n) (p : A) :
    (mixedScalarPadMap f i p).val = (Function.update p.val.1 i ((f p).val 0),p.val.2) := by
  change ((vfTupleAssembleMap A n
    (fun k => if k = i then f else (vfTupleSelectMap S (fun _ : Fin 1 => k)).comp (mixedVFHeadMap A)) p).val,
    p.val.2) = _
  apply Prod.ext
  · rw [vfTupleAssembleMap_value]
    funext k
    by_cases hk : k = i
    · subst k
      simp only [ite_true,Function.update_self]
    · simp only [if_neg hk,Function.update_of_ne hk]
      rfl
  · rfl

def HasMixedVFScalarDerivativeAt {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : A)
    (L : (Fin n → VF M) →ₗ[VF M] (Fin 1 → VF M)) : Prop :=
  ∃ F : (Fin n → VF M) → Fin 1 → VF M,
    (∃ ρ : Gamma M, ∀ x : Fin n → VF M, x ∈ vfBall p.val.1 ρ →
      ∃ hx : (x,p.val.2) ∈ A.carrier, (f ⟨(x,p.val.2),hx⟩).val = F x) ∧
    HasVFDerivativeAt F p.val.1 L

theorem scalarDerivative_of_pad_derivative {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (i : Fin n) (p : A)
    {L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M)} (hL : HasMixedVFDerivativeAt (mixedScalarPadMap f i) p L) :
    ∃ D, HasMixedVFScalarDerivativeAt f p D := by
  obtain ⟨F,⟨ρ,hρ⟩,hF⟩ := hL
  let D : (Fin n → VF M) →ₗ[VF M] (Fin 1 → VF M) :=
    LinearMap.pi (fun _ => (LinearMap.proj i).comp L)
  refine ⟨D,(fun x _ => F x i),⟨ρ,fun x hx => ?_⟩,?_⟩
  · obtain ⟨hxA,hxF⟩ := hρ x hx
    refine ⟨hxA,?_⟩
    have h := congrArg (fun z : Mixed M n r => z.1 i) hxF
    rw [mixedScalarPadMap_value] at h
    change Function.update x i ((f ⟨(x,p.val.2),hxA⟩).val 0) i = F x i at h
    rw [Function.update_self] at h
    funext j
    fin_cases j
    exact h
  · apply hasVFDerivativeAt_of_components
    intro j
    exact hF.component i

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_small_rv_labels_for_scalar_differentiability
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : MeasuredRVObject (M := M) S (n+1)) {I : Type} [Finite I]
    (f : I → Map (rvLift U.object) (DefSet.univ (rawVFSpace (M := M) 1) S)) :
    ∃ D : DefSet (rawRVSpace (M := M) U.object.arity) S, D.carrier ⊆ U.object.domain.carrier ∧
      rvDim D < n+1 ∧ ∀ p : rvLift U.object, p.val.2 ∉ D.carrier →
        ∀ i, ∃ L, HasMixedVFScalarDerivativeAt (f i) p L := by
  obtain ⟨D,hD,hDim,hGood⟩ := exists_small_rv_labels_for_mixed_differentiability h00 hc hκ hs hsmall hΓ hv U
    (fun _ : I => U.object.arity)
    (fun _ : I => DefSet.univ (rawMixedSpace (M := M) (n+1) U.object.arity) S)
    (fun i => mixedScalarPadMap (f i) (0 : Fin (n+1)))
  refine ⟨D,hD,hDim,fun p hp i => ?_⟩
  obtain ⟨L,hL⟩ := hGood p hp i
  exact scalarDerivative_of_pad_derivative (f i) 0 p hL

end DiamondIntegral.Section6
