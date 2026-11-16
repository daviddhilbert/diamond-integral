import «section 6».UnaryCenterMap

/-! Centers for a finite original-base definable RV set, including its
zero fiber. This is the zero-input case of the parametric construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_rv_centers
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (C : Set M) (hC : S.Definable₁ LRV C) (hFin : C.Finite) (hRV : ∀ v ∈ C, iRV v) :
    ∃ f : (Fin 1 → M) → VF M, S.DefinableFun LRV (fun z => (f z).val) ∧
      ∀ v ∈ C, iRv (f (fun _ => v)).val = v := by
  have hA : S.Definable LRV (vfValues '' (Set.univ : Set (Fin 0 → VF M))) := by
    convert vfRawUniverse_definable S 0 using 1
    ext z
    exact ⟨by rintro ⟨a,_,rfl⟩ i; exact (a i).property,
      fun h => ⟨(fun i => ⟨z i,h i⟩),Set.mem_univ _,rfl⟩⟩
  obtain ⟨f,hf,hval⟩ := exists_parametric_rv_centers hc h00 hs hv V S hV hVS hSV hnt hsmall
    Set.univ hA (fun _ : Fin 0 → M => C) (hC.preimage_comp (Sum.inr : Fin 1 → Fin 0 ⊕ Fin 1))
    (fun _ => hFin) (fun _ => hRV)
  refine ⟨f,hf,fun v hvC => ?_⟩
  have h := hval (Fin.elim0 : Fin 0 → VF M) (Set.mem_univ _) v hvC
  have he : Fin.snoc (vfValues (Fin.elim0 : Fin 0 → VF M)) v = (fun _ : Fin 1 => v) := by
    funext i
    fin_cases i
    rfl
  rwa [he] at h

end DiamondIntegral.Section6
