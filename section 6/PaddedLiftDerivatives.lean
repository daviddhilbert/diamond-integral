import «section 6».PaddedLiftMaps
import «section 6».AffineTailDifferentiability

/-! Carrying an identity VF tail retains full total derivatives and
the exact full head determinant. All head dependencies are included. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k m : ℕ}

def carryIdentityTail (f : (Fin k → VF M) → Fin k → VF M) (m : ℕ)
    (z : Fin (k+m) → VF M) : Fin (k+m) → VF M :=
  productTuple (f (z ∘ productLeft k m)) (z ∘ productRight k m)

theorem vfdifferentiableAt_carryIdentityTail (f : (Fin k → VF M) → Fin k → VF M)
    (a : Fin (k+m) → VF M) (hf : VFDifferentiableAt f (a ∘ productLeft k m)) :
    VFDifferentiableAt (carryIdentityTail f m) a := by
  obtain ⟨L,hL⟩ := hf
  obtain ⟨H,hH⟩ := vfdifferentiableAt_select (productLeft k m) a
  have hHead : VFDifferentiableAt (fun z => f (z ∘ productLeft k m)) a :=
    ⟨L.comp H,HasVFDerivativeAt.comp (M := M) (f := fun z => z ∘ productLeft k m) (g := f) hL hH⟩
  apply vfdifferentiableAt_components
  intro i
  obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin (k+m)).surjective i
  cases j with
  | inl j =>
    change VFDifferentiableAt (fun z (_ : Fin 1) => carryIdentityTail f m z (productLeft k m j)) a
    simp only [carryIdentityTail,productTuple_left]
    exact VFDifferentiableAt.select (M := M) hHead (fun _ : Fin 1 => j)
  | inr j =>
    change VFDifferentiableAt (fun z (_ : Fin 1) => carryIdentityTail f m z (productRight k m j)) a
    simp only [carryIdentityTail,productTuple_right]
    exact vfdifferentiableAt_select (fun _ : Fin 1 => productRight k m j) a

theorem carryIdentityTail_derivative_det (f : (Fin k → VF M) → Fin k → VF M)
    (a : Fin (k+m) → VF M)
    {D : (Fin (k+m) → VF M) →ₗ[VF M] (Fin (k+m) → VF M)}
    {L : (Fin k → VF M) →ₗ[VF M] (Fin k → VF M)}
    (hD : HasVFDerivativeAt (carryIdentityTail f m) a D)
    (hL : HasVFDerivativeAt f (a ∘ productLeft k m) L) :
    (LinearMap.toMatrix' D).det=(LinearMap.toMatrix' L).det := by
  let x := a ∘ productLeft k m
  let y := a ∘ productRight k m
  have ha : productTuple x y=a := productTuple_ext (fun i => productTuple_left _ _ i) (fun j => productTuple_right _ _ j)
  have he : liftWithAffineTail f (fun _ => (0 : Fin m → VF M)) (fun _ => 0) (fun _ _ => 1)=carryIdentityTail f m := by
    funext z
    apply productTuple_ext
    · intro i
      simp only [liftWithAffineTail,carryIdentityTail,productTuple_left]
    · intro j
      simp only [liftWithAffineTail,carryIdentityTail,productTuple_right,affineTail,Pi.zero_apply,sub_zero,one_mul,zero_add]
  have h := det_liftWithAffineTail (carryIdentityTail f m) f (fun _ => (0 : Fin m → VF M))
    (fun _ => 0) (fun _ _ => 1) x y D L (ha.symm ▸ hD) hL 1 (fun z _ => congrFun he z)
  simpa only [Finset.prod_const_one,mul_one] using h

theorem paddedRVLiftMap_derivative_and_det {U V : MeasuredRVObject (M := M) S k}
    (f : Map (rvLift U.object) (rvLift V.object)) (m : ℕ)
    (p : rvLift (measuredRVPadOnes U m).object)
    {L : (Fin k → VF M) →ₗ[VF M] (Fin k → VF M)}
    (hL : HasMixedVFDerivativeAt f (rvPadOnesLiftHeadMap U m p) L) :
    ∃ D,HasMixedVFDerivativeAt (paddedRVLiftMap f m) p D ∧
      (LinearMap.toMatrix' D).det=(LinearMap.toMatrix' L).det := by
  let H := rvPadOnesLiftHeadMap U m
  obtain ⟨F,⟨ρ,hρ⟩,hF⟩ := hL
  obtain ⟨D,hD⟩ := vfdifferentiableAt_carryIdentityTail F p.val.1 ⟨L,hF⟩
  obtain ⟨σ,hσ⟩ := exists_fixed_label_ball_in_rvLift (measuredRVPadOnes U m) p
  refine ⟨D,⟨carryIdentityTail F m,⟨max σ ρ,fun z hz => ?_⟩,hD⟩,
    carryIdentityTail_derivative_det F p.val.1 hD hF⟩
  have hzU := hσ z (vfBall_anti (le_max_left σ ρ) hz)
  let q : rvLift (measuredRVPadOnes U m).object := ⟨(z,p.val.2),hzU⟩
  have hzH : z ∘ productLeft k m ∈ vfBall (H p).val.1 ρ :=
    fun i => (vfBall_anti (le_max_right σ ρ) hz) (productLeft k m i)
  obtain ⟨hzF,hval⟩ := hρ (z ∘ productLeft k m) hzH
  have hq : H q=⟨(z ∘ productLeft k m,(H p).val.2),hzF⟩ := Subtype.ext rfl
  refine ⟨hzU,?_⟩
  change (paddedRVLiftMap f m q).val=_
  rw [paddedRVLiftMap_value,hq,hval]
  rfl

end DiamondIntegral.Section6
