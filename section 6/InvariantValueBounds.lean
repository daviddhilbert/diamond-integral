import «section 6».PartialFocusGraphTemplates

/-! Invariant domains avoiding coordinate zero have VF values bounded
above by their own invariant radii. This gives named bounds without
assuming cofinality of the original base's value group. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem AlphaInvariant.value_le_radius {A : Set (Fin n → VF M)} {α : Fin n → Gamma M}
    (hA : AlphaInvariant α A) (hNZ : ∀ a ∈ A,∀ i,a i ≠ 0) (a : Fin n → VF M) (ha : a ∈ A) (i : Fin n) :
    vfValue (a i) ≤ (α i).val := by
  by_contra hn
  have hlt : (α i).val < vfValue (a i) := lt_of_not_ge hn
  have hClose : Congruent α a (Function.update a i 0) := by
    intro j
    by_cases hj : j=i
    · subst j
      simpa only [Function.update_self,sub_zero] using hlt
    · simp only [Function.update_of_ne hj,sub_self]
      exact gamma_lt_value_zero (α j)
  have hmem := (hA a (Function.update a i 0) hClose).mp ha
  exact hNZ _ hmem i (Function.update_self i 0 a)

theorem properInvariant_uniform_named_upper_vf_bound
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : Set (Mixed M n r)} (hA : ProperInvariant S A) (hD : VFDoublyBounded A) :
    ∃ δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧ 1 ≤ δ ∧
      (∀ u,AlphaInvariant (fun _ => δ) (vfFibre A u)) ∧
      ∀ p ∈ A,∀ i,vfValue (p.1 i) ≤ δ.val := by
  obtain ⟨δ,hδ,hδ1,hInv⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hA
  refine ⟨δ,hδ,hδ1,hInv,fun p hp i => ?_⟩
  exact (hInv p.2).value_le_radius (fun a ha j => hD.nonzero ha j) p.1 hp i

theorem AlphaInvariant.combine_coordinate_radius {A : Set (Fin n → VF M)}
    (η β α : Gamma M) (j : Fin n) (hη : AlphaInvariant (fun _ => η) A) (hηβ : η ≤ β)
    (hActive : ∀ a ∈ A,∀ x,α.val < vfValue (a j-x) → Function.update a j x ∈ A) :
    AlphaInvariant (fun i => if i=j then α else β) A := by
  have step (a b : Fin n → VF M) (hab : Congruent (fun i => if i=j then α else β) a b) (ha : a ∈ A) : b ∈ A := by
    let c := Function.update b j (a j)
    have hClose : Congruent (fun _ => η) a c := by
      intro i
      by_cases hi : i=j
      · subst i
        simp only [c,Function.update_self,sub_self]
        exact gamma_lt_value_zero η
      · have h := hab i
        simp only [if_neg hi] at h
        exact (show η.val ≤ β.val from hηβ).trans_lt (by simpa only [c,Function.update_of_ne hi] using h)
    have hc := (hη a c hClose).mp ha
    have hCut : α.val < vfValue (c j-b j) := by
      simpa only [c,Function.update_self,if_pos rfl,ite_true] using hab j
    have hmem := hActive c hc (b j) hCut
    simpa only [c,Function.update_idem,Function.update_eq_self] using hmem
  intro a b hab
  exact ⟨step a b hab,step b a hab.symm⟩

theorem CentripetalData.coordinate_cutoff_stable
    {A : DefSet (rawMixedSpace (M := M) n r) S} (D : CentripetalData (G := G) A)
    (p : Mixed M n r) (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) (x : VF M)
    (hClose : vfValue (D.coefficient*D.extendedFocus p)<vfValue (p.1 D.coordinate-x)) :
    (Function.update p.1 D.coordinate x,p.2) ∈ A.carrier := by
  obtain ⟨α,β,hα,hβ,hInv,hCov,hDom⟩ := D.covariance p.2 hu
  have hBound := hDom p.1 hp
  rw [← D.extendedFocus_active hp hu] at hBound
  apply (hInv p.1 (Function.update p.1 D.coordinate x) ?_).mp hp
  intro i
  by_cases hi : i=D.coordinate
  · subst i
    simpa only [if_pos rfl,ite_true,Function.update_self] using hBound.trans_lt hClose
  · simp only [if_neg hi,Function.update_of_ne hi,sub_self]
    exact gamma_lt_value_zero (β i)

end DiamondIntegral.Section6
