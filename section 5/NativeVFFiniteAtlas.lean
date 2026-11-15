import «section 5».NativeVFCoproductRealization
import «section 5».NativeGroundRVLabels

/-! Finite native VF charts have one actual tagged realization, with
original-ground definable inclusions and no added chart parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def nativeVFFiniteSum : (N : ℕ) → (Fin N → GammaGroundFiniteVFObject hc B) → GammaGroundFiniteVFObject hc B
  | 0,_ => GammaGroundFiniteVFObject.empty hc B
  | N+1,A => (A 0).coprod (nativeVFFiniteSum N (fun i => A i.succ))

def finiteDependentSumHeadEquiv {N : ℕ} (D : Fin (N+1) → Type) :
    (Σ i,D i) ≃ D 0 ⊕ (Σ i : Fin N,D i.succ) where
  toFun a := Fin.cases (fun x => Sum.inl x) (fun i x => Sum.inr ⟨i,x⟩) a.1 a.2
  invFun a := match a with
    | .inl x => ⟨0,x⟩
    | .inr x => ⟨x.1.succ,x.2⟩
  left_inv a := by
    rcases a with ⟨i,x⟩
    revert x
    refine Fin.cases ?_ (fun i => ?_) i <;> intro x <;> rfl
  right_inv a := by cases a <;> rfl

def nativeVFFiniteSumEquiv : (N : ℕ) → (A : Fin N → GammaGroundFiniteVFObject hc B) →
    (Σ i,(A i).domain) ≃ (nativeVFFiniteSum N A).domain
  | 0,A => {
      toFun a := a.1.elim0
      invFun x := False.elim x.property
      left_inv a := a.1.elim0
      right_inv x := False.elim x.property }
  | N+1,A => (finiteDependentSumHeadEquiv (fun i => (A i).domain)).trans
      ((Equiv.sumCongr (Equiv.refl _) (nativeVFFiniteSumEquiv N (fun i => A i.succ))).trans
        (nativeVFCoproductEquiv (A 0) (nativeVFFiniteSum N (fun i => A i.succ))))

def nativeVFFiniteSumInclusion : (N : ℕ) → (A : Fin N → GammaGroundFiniteVFObject hc B) →
    (i : Fin N) → GammaGroundMap (A i).domain (nativeVFFiniteSum N A).domain
  | 0,_,i => i.elim0
  | N+1,A,i => Fin.cases
      (nativeVFCoproductLeft (A 0) (nativeVFFiniteSum N (fun i => A i.succ)))
      (fun j => (nativeVFCoproductRight (A 0) (nativeVFFiniteSum N (fun i => A i.succ))).comp
        (nativeVFFiniteSumInclusion N (fun i => A i.succ) j)) i

theorem nativeVFFiniteSumInclusion_value : ∀ (N : ℕ) (A : Fin N → GammaGroundFiniteVFObject hc B)
    (i : Fin N) (a : (A i).domain),
    nativeVFFiniteSumInclusion N A i a = nativeVFFiniteSumEquiv N A ⟨i,a⟩ := by
  intro N
  induction N with
  | zero => intro A i; exact i.elim0
  | succ N ih =>
    intro A i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro a
      rfl
    · intro a
      change nativeVFCoproductRight (A 0) (nativeVFFiniteSum N (fun i => A i.succ))
        (nativeVFFiniteSumInclusion N (fun i => A i.succ) j a) = _
      rw [ih]
      rfl

theorem nativeVFFiniteSum_groundLabels {G : GammaGroundContext M} :
    ∀ (N : ℕ) (A : Fin N → GammaGroundFiniteVFObject hc G.base),
      (∀ i,NativeGroundRVLabels (A i).domain) → NativeGroundRVLabels (nativeVFFiniteSum N A).domain := by
  intro N
  induction N with
  | zero => intro A hA; exact NativeGroundRVLabels.pureVF _
  | succ N ih =>
    intro A hA
    exact (hA 0).coprod (ih (fun i => A i.succ) (fun i => hA i.succ))

end DiamondIntegral.Section5
