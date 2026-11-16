import «section 6».ContinuousRVGraphTemplates

/-! First-order scalar levels of complete RV-family graph templates.
These retain the entire graph and all RV labels when describing the
indicator conditions used in finite formula selection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p r n : ℕ}

def forallRawParameterLocus {ι κ : Type} (R : Set (ι ⊕ κ → M)) : Set (ι → M) :=
  {a | ∀ z,Sum.elim a z ∈ R}

theorem forallRawParameterLocus_definable {ι κ : Type} [Finite ι] [Finite κ]
    (R : Set (ι ⊕ κ → M)) (hR : S.Definable LRV R) : S.Definable LRV (forallRawParameterLocus R) := by
  convert (hR.compl.exists_of_finite).compl using 1
  ext a
  change (∀ z,Sum.elim a z ∈ R) ↔ ¬ ∃ z,Sum.elim a z ∉ R
  simp only [not_exists,not_not]

theorem rawVFZero_constant_definable {ι : Type} : S.DefinableFun LRV (fun _ : ι → M => iVFZero) := by
  have h := (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfZero)).comp
    (show S.DefinableMap LRV (fun _ : ι → M => (Fin.elim0 : Fin 0 → M)) from fun i => i.elim0)
  exact h

theorem rawVFOne_constant_definable {ι : Type} : S.DefinableFun LRV (fun _ : ι → M => iVFOne) := by
  have h := (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfOne)).comp
    (show S.DefinableMap LRV (fun _ : ι → M => (Fin.elim0 : Fin 0 → M)) from fun i => i.elim0)
  exact h

def rvScalarTemplateFill (c : M) (z : Fin p ⊕ (Fin r ⊕ Fin n) → M) :
    Fin p ⊕ (Fin r ⊕ (Fin n ⊕ Fin 1)) → M :=
  Sum.elim (z ∘ Sum.inl) (Sum.elim (z ∘ Sum.inr ∘ Sum.inl)
    (Sum.elim (z ∘ Sum.inr ∘ Sum.inr) (fun _ : Fin 1 => c)))

def rvScalarTemplateLevel (T : ContinuousRVGraphTemplate (M := M) S p r n 1) (c : M) :
    Set (Fin p ⊕ (Fin r ⊕ Fin n) → M) := {z | rvScalarTemplateFill c z ∈ T.graph}

theorem rvScalarTemplateLevel_definable
    (T : ContinuousRVGraphTemplate (M := M) S p r n 1) (c : M)
    (hC : S.DefinableFun LRV (fun _ : Fin p ⊕ (Fin r ⊕ Fin n) → M => c)) :
    S.Definable LRV (rvScalarTemplateLevel T c) := by
  apply T.definable.preimage_map
  rintro (i | (i | (i | i)))
  · exact Set.DefinableFun.proj LRV
  · exact Set.DefinableFun.proj LRV
  · exact Set.DefinableFun.proj LRV
  · exact hC

theorem rvScalarTemplateLevel_at
    (T : ContinuousRVGraphTemplate (M := M) S p r n 1) (a : Fin p → M) (ha : a ∈ T.good)
    (u : Fin r → RVInfinity M) (x : Fin n → VF M) (c : M) :
    Sum.elim a (Sum.elim (rvValues u) (vfValues x)) ∈ rvScalarTemplateLevel T c ↔
      ((T.value a ha u x) 0).val=c := by
  change Sum.elim a (Sum.elim (rvValues u) (Sum.elim (vfValues x) (fun _ : Fin 1 => c))) ∈ T.graph ↔ _
  constructor
  · intro h
    have he := (T.rowGood a ha u).1.2 (vfValues x) (fun _ : Fin 1 => c)
      (vfValues (T.value a ha u x)) h (T.value_mem a ha u x)
    exact (congrFun he 0).symm
  · intro h
    have hCodes : vfValues (T.value a ha u x)=(fun _ : Fin 1 => c) := by
      funext i
      have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact h
    have hMem := T.value_mem a ha u x
    rw [hCodes] at hMem
    exact hMem

end DiamondIntegral.Section6
