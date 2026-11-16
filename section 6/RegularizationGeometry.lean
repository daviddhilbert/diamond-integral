import «section 6».ProperComposition
import «section 6».MixedJacobianLocus

/-! Regularization retains all old tags and attaches the current VF
leading terms. Double bounds keep those new tags away from RV zero. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ}

def VFDoublyBounded (A : Set (Mixed M n r)) : Prop :=
  ∃ γ : Gamma M, ∀ p ∈ A, ∀ i,
    (γ⁻¹).val ≤ vfValue (p.1 i) ∧ vfValue (p.1 i) ≤ γ.val

theorem VFDoublyBounded.nonzero {A : Set (Mixed M n r)} (hA : VFDoublyBounded A)
    {p : Mixed M n r} (hp : p ∈ A) (i : Fin n) : p.1 i ≠ 0 := by
  obtain ⟨γ,hγ⟩ := hA
  intro he
  have h := (hγ p hp i).2
  rw [he,value_zero] at h
  exact γ.property (le_antisymm (Values.le_infinity _) h)

def regularize (p : Mixed M n r) : Mixed M n (n+r) :=
  (p.1,Fin.append (tupleRV M p.1) p.2)

theorem regularize_injective : Function.Injective (regularize (M := M) (n := n) (r := r)) := by
  intro a b he
  have hVF : a.1 = b.1 := congrArg (fun q : Mixed M n (n+r) => q.1) he
  have hRV : a.2 = b.2 := funext (fun i => by
    simpa only [regularize,Fin.append_right] using congrArg (fun p : Mixed M n (n+r) => p.2 (Fin.natAdd n i)) he)
  exact Prod.ext hVF hRV

theorem regularized_fibre (A : Set (Mixed M n r)) (v : Fin (n+r) → RVInfinity M) :
    vfFibre (regularize '' A) v = vfFibre A (v ∘ Fin.natAdd n) ∩
      {a | tupleRV M a = v ∘ Fin.castAdd r} := by
  ext a
  constructor
  · rintro ⟨p,hp,he⟩
    have hVF : p.1 = a := congrArg Prod.fst he
    have hOld : p.2 = v ∘ Fin.natAdd n := funext (fun i => by
      simpa only [regularize,Fin.append_right,Function.comp_apply] using
        congrArg (fun q : Mixed M n (n+r) => q.2 (Fin.natAdd n i)) he)
    have hNew : tupleRV M p.1 = v ∘ Fin.castAdd r := funext (fun i => by
      simpa only [regularize,Fin.append_left,Function.comp_apply] using
        congrArg (fun q : Mixed M n (n+r) => q.2 (Fin.castAdd r i)) he)
    exact ⟨by change (a,v ∘ Fin.natAdd n) ∈ A; rw [← hVF,← hOld]; exact hp,hVF ▸ hNew⟩
  · rintro ⟨ha,hRV⟩
    refine ⟨(a,v ∘ Fin.natAdd n),ha,Prod.ext rfl ?_⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [regularize,Fin.append_left,Function.comp_apply] using congrFun hRV i
    · simp only [regularize,Fin.append_right,Function.comp_apply]

theorem AlphaInvariant.inter_rv_fibre {α : Fin n → Gamma M}
    {A : Set (Fin n → VF M)} (hA : AlphaInvariant α A) (γ : Gamma M)
    (hbound : ∀ a ∈ A, ∀ i, vfValue (a i) ≤ γ.val) (t : Fin n → RVInfinity M) :
    AlphaInvariant (fun i => max (α i) γ) (A ∩ {a | tupleRV M a = t}) := by
  have step (a b : Fin n → VF M) (hab : Congruent (fun i => max (α i) γ) a b)
      (ha : a ∈ A ∩ {a | tupleRV M a = t}) : b ∈ A ∩ {a | tupleRV M a = t} := by
    refine ⟨(hA a b (hab.of_larger_radius (fun i => le_max_left _ _))).mp ha.1,?_⟩
    have he : tupleRV M b = tupleRV M a := by
      funext i
      exact rv_eq_of_close_at_radius γ (hbound a ha.1 i)
        ((show γ.val ≤ (max (α i) γ).val from le_max_right _ _).trans_lt (hab.symm i))
    exact he.trans ha.2
  intro a b hab
  exact ⟨step a b hab,step b a hab.symm⟩

theorem regularized_vfBounded {A : Set (Mixed M n r)} (hA : VFBounded A) :
    VFBounded (regularize '' A) := by
  obtain ⟨γ,hγ⟩ := hA
  exact ⟨γ,by rintro _ ⟨p,hp,rfl⟩ i; exact hγ p hp i⟩

theorem regularized_rvBounded {A : Set (Mixed M n r)}
    (hVF : VFDoublyBounded A) (hRV : RVSupportDoublyBounded A) :
    RVSupportDoublyBounded (regularize '' A) := by
  obtain ⟨γ,hγ⟩ := hVF
  obtain ⟨δ,hδ⟩ := hRV
  refine ⟨max γ δ,?_⟩
  rintro _ ⟨p,hp,rfl⟩ i
  have hlowγ : ((max γ δ)⁻¹).val ≤ (γ⁻¹).val :=
    show (max γ δ)⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left γ δ)
  have hlowδ : ((max γ δ)⁻¹).val ≤ (δ⁻¹).val :=
    show (max γ δ)⁻¹ ≤ δ⁻¹ from inv_le_inv' (le_max_right γ δ)
  have hhighγ : γ.val ≤ (max γ δ).val := le_max_left γ δ
  have hhighδ : δ.val ≤ (max γ δ).val := le_max_right γ δ
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · change ((max γ δ)⁻¹).val ≤ Values.vrv ((regularize p).2 (Fin.castAdd r i)) ∧
      Values.vrv ((regularize p).2 (Fin.castAdd r i)) ≤ (max γ δ).val
    simp only [regularize,Fin.append_left]
    exact ⟨hlowγ.trans (hγ p hp i).1,(hγ p hp i).2.trans hhighγ⟩
  · change ((max γ δ)⁻¹).val ≤ Values.vrv ((regularize p).2 (Fin.natAdd n i)) ∧
      Values.vrv ((regularize p).2 (Fin.natAdd n i)) ≤ (max γ δ).val
    simp only [regularize,Fin.append_right]
    exact ⟨hlowδ.trans (hδ p hp i).1,(hδ p hp i).2.trans hhighδ⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem regularized_clopen_fibres
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} {A : Set (Mixed M n r)} (hA : ProperInvariant S A) (hVF : VFDoublyBounded A)
    (v : Fin (n+r) → RVInfinity M) : IsClopen (vfFibre (regularize '' A) v) := by
  rw [regularized_fibre]
  obtain ⟨α,hαdef,hα⟩ := hA.radii (v ∘ Fin.natAdd n)
  obtain ⟨γ,hγ⟩ := hVF
  exact (hα.inter_rv_fibre γ (fun a ha i => (hγ (a,v ∘ Fin.natAdd n) ha i).2)
    (v ∘ Fin.castAdd r)).isClopen hv

end DiamondIntegral.Section6
