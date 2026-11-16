import «section 6».MixedTupleDifferentiability
import Section9.PolynomialDifferentiation
import Section9.AffineTailJacobian

/-! Full total differentiability of an affine tail whose coefficients
depend differentiably on the head. The derivative includes all head
dependencies, rather than just the separate coordinate derivatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m k q : ℕ}

def vfSelectLinear (v : Fin m → Fin n) : (Fin n → VF M) →ₗ[VF M] (Fin m → VF M) :=
  LinearMap.pi (fun i => LinearMap.proj (v i))

theorem vfSelectLinear_apply (v : Fin m → Fin n) (x : Fin n → VF M) :
    vfSelectLinear v x = x ∘ v := rfl

theorem vfdifferentiableAt_select (v : Fin m → Fin n) (p : Fin n → VF M) :
    VFDifferentiableAt (fun x : Fin n → VF M => x ∘ v) p := by
  refine ⟨vfSelectLinear v,?_⟩
  simpa only [add_zero,vfSelectLinear_apply] using hasVFDerivativeAt_affine (vfSelectLinear v) 0 p

theorem VFDifferentiableAt.select {f : (Fin n → VF M) → Fin m → VF M}
    {p : Fin n → VF M} (hf : VFDifferentiableAt f p) (v : Fin q → Fin m) :
    VFDifferentiableAt (fun x => f x ∘ v) p := by
  obtain ⟨L,hL⟩ := hf
  obtain ⟨D,hD⟩ := vfdifferentiableAt_select v (f p)
  exact ⟨D.comp L,hD.comp hL⟩

theorem vfdifferentiableAt_components {f : (Fin n → VF M) → Fin m → VF M}
    {p : Fin n → VF M}
    (h : ∀ i, VFDifferentiableAt (fun x (_ : Fin 1) => f x i) p) :
    VFDifferentiableAt f p := by
  choose L hL using h
  let D := LinearMap.pi (fun i => (LinearMap.proj (0 : Fin 1)).comp (L i))
  exact ⟨D,hasVFDerivativeAt_of_components D (fun i => (hL i).component 0)⟩

theorem VFDifferentiableAt.polynomial {f : (Fin n → VF M) → Fin q → VF M}
    {p : Fin n → VF M} (hf : VFDifferentiableAt f p)
    (P : Fin m → MvPolynomial (Fin q) (VF M)) :
    VFDifferentiableAt (fun x i => aeval (f x) (P i)) p := by
  obtain ⟨L,hL⟩ := hf
  exact ⟨_,(hasVFDerivativeAt_aeval P (f p)).comp hL⟩

theorem vfdifferentiableAt_liftWithAffineTail
    (F : (Fin k → VF M) → Fin k → VF M)
    (a b c : (Fin k → VF M) → Fin m → VF M) (p : Fin (k+m) → VF M)
    (hF : VFDifferentiableAt F (p ∘ productLeft k m))
    (ha : VFDifferentiableAt a (p ∘ productLeft k m))
    (hb : VFDifferentiableAt b (p ∘ productLeft k m))
    (hc : VFDifferentiableAt c (p ∘ productLeft k m)) :
    VFDifferentiableAt (liftWithAffineTail F a b c) p := by
  let l : Fin k → Fin (k+m) := productLeft k m
  let r : Fin m → Fin (k+m) := productRight k m
  obtain ⟨H,hH⟩ := vfdifferentiableAt_select l p
  have hFH : VFDifferentiableAt (fun z => F (z ∘ l)) p := by
    obtain ⟨L,hL⟩ := hF
    exact ⟨L.comp H,HasVFDerivativeAt.comp (M := M)
      (f := fun z => z ∘ l) (g := F) (a := p) hL hH⟩
  have haH : VFDifferentiableAt (fun z => a (z ∘ l)) p := by
    obtain ⟨L,hL⟩ := ha
    exact ⟨L.comp H,HasVFDerivativeAt.comp (M := M)
      (f := fun z => z ∘ l) (g := a) (a := p) hL hH⟩
  have hbH : VFDifferentiableAt (fun z => b (z ∘ l)) p := by
    obtain ⟨L,hL⟩ := hb
    exact ⟨L.comp H,HasVFDerivativeAt.comp (M := M)
      (f := fun z => z ∘ l) (g := b) (a := p) hL hH⟩
  have hcH : VFDifferentiableAt (fun z => c (z ∘ l)) p := by
    obtain ⟨L,hL⟩ := hc
    exact ⟨L.comp H,HasVFDerivativeAt.comp (M := M)
      (f := fun z => z ∘ l) (g := c) (a := p) hL hH⟩
  apply vfdifferentiableAt_components
  intro j
  obtain ⟨ij,rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin (k+m)).surjective j
  cases ij with
  | inl i =>
      change VFDifferentiableAt (fun z (_ : Fin 1) => liftWithAffineTail F a b c z (productLeft k m i)) p
      simpa only [liftWithAffineTail,productTuple_left,Function.comp_def,l] using
        VFDifferentiableAt.select (M := M) hFH (fun _ : Fin 1 => i)
  | inr i =>
      let u (z : Fin (k+m) → VF M) : Fin 4 → VF M :=
        ![b (z ∘ l) i,c (z ∘ l) i,z (r i),a (z ∘ l) i]
      have hu : VFDifferentiableAt u p := by
        apply vfdifferentiableAt_components
        intro j
        fin_cases j
        · exact VFDifferentiableAt.select hbH (fun _ : Fin 1 => i)
        · exact VFDifferentiableAt.select hcH (fun _ : Fin 1 => i)
        · exact vfdifferentiableAt_select (fun _ : Fin 1 => r i) p
        · exact VFDifferentiableAt.select haH (fun _ : Fin 1 => i)
      let P : Fin 1 → MvPolynomial (Fin 4) (VF M) := fun _ => X 0 + X 1 * (X 2 - X 3)
      change VFDifferentiableAt (fun z (_ : Fin 1) => liftWithAffineTail F a b c z (productRight k m i)) p
      simp only [liftWithAffineTail,productTuple_right]
      have hp := VFDifferentiableAt.polynomial (M := M) (n := k+m) (q := 4) (m := 1)
        (f := u) (p := p) hu P
      have he : (fun z (_ : Fin 1) =>
          affineTail (a (z ∘ productLeft k m)) (b (z ∘ productLeft k m))
            (c (z ∘ productLeft k m)) (z ∘ productRight k m) i) =
          (fun z j => aeval (u z) (P j)) := by
        funext z j
        dsimp only [P]
        rw [map_add,map_mul,map_sub,aeval_X,aeval_X,aeval_X,aeval_X]
        rfl
      rw [he]
      exact hp

end DiamondIntegral.Section6
