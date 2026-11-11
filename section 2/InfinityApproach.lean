import «section 2».CorrespondencePullback

/-!
# Uniform families escaping toward projective infinity

The condition is a field valuation comparison on y*c. It is equivalent to
val(y) < -val(c) for nonzero c and uses no chosen Gamma representative.
The full raw LRV graph is definable over the original base.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

def vfInfinitySide (r y : VF M) : Prop := ¬ VFValued.predV (y*r) 1

def vfEscape (B : Set (Fin m → VF M)) (c : Fin 1 → VF M) : Set (Fin m → VF M) :=
  {y ∈ B | ∃ i, vfInfinitySide (c 0) (y i)}

theorem vfInfinitySide_iff (r y : VF M) (hr : r ≠ 0) :
    vfInfinitySide r y ↔ memLimitBall none (finiteValue r hr) y := by
  rw [← memValuedLimitSide_iff_memLimitBall r (finiteValue r hr) rfl none y]
  change (¬ VFValued.predV (y*r) 1) ↔
    (Values.presentationValuation (M := M) r)⁻¹ < Values.presentationValuation y
  rw [Values.presentation_compatible,map_mul,map_one,not_le,← one_div]
  exact (div_lt_iff₀ (pos_iff_ne_zero.mpr
    ((Values.presentationValuation (M := M)).ne_zero_iff.mpr hr))).symm

theorem vfInfinitySide_raw_definable (S : Set M) {ι : Type} (r y : ι) :
    S.Definable LRV {z : ι → M | ¬ iLe (iRv iVFOne) (iRv (iVFMul (z y) (z r)))} := by
  have hmul : S.DefinableFun LRV (fun z : ι → M => iVFMul (z y) (z r)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfMul)).comp
      (show S.DefinableMap LRV (fun z : ι → M => ![z y,z r]) from by
        intro j
        fin_cases j <;> exact Set.DefinableFun.proj LRV)
  have hone : S.DefinableFun LRV (fun _ : ι → M => iVFOne) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfOne Fin.elim0 (fun i => i.elim0))
  have hrv {f : (ι → M) → M} (hf : S.DefinableFun LRV f) :
      S.DefinableFun LRV (fun z => iRv (f z)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun z : ι → M => ![f z]) from by
        intro j
        fin_cases j
        exact hf)
  exact ((GammaParameters.raw_le_definable S).preimage_map
    (show S.DefinableMap LRV (fun z : ι → M => ![iRv iVFOne,iRv (iVFMul (z y) (z r))]) from by
      intro j
      fin_cases j
      · exact hrv hone
      · exact hrv hmul)).compl

theorem vfEscape_graph_definable {S : Set M}
    (U : Set (Fin 1 → VF M)) (hU : S.Definable LRV (vfValues '' U))
    (B : Set (Fin m → VF M)) (hB : S.Definable LRV (vfValues '' B)) :
    S.Definable LRV (vfCorrespondenceGraph U (vfEscape B)) := by
  have hSome := Set.definable_iUnion_of_finite (fun i : Fin m =>
    vfInfinitySide_raw_definable S (Sum.inl 0 : Fin 1 ⊕ Fin m) (Sum.inr i))
  have h := ((hU.preimage_comp (Sum.inl : Fin 1 → Fin 1 ⊕ Fin m)).inter
    (hB.preimage_comp (Sum.inr : Fin m → Fin 1 ⊕ Fin m))).inter hSome
  convert h using 1
  ext z
  simp only [Set.mem_inter_iff,Set.mem_iUnion,Set.mem_ofPred_eq]
  change (∃ c ∈ U, ∃ y ∈ vfEscape B c, Sum.elim (vfValues c) (vfValues y) = z) ↔
    (z ∘ Sum.inl ∈ vfValues '' U ∧ z ∘ Sum.inr ∈ vfValues '' B) ∧
      ∃ i, ¬ iLe (iRv iVFOne) (iRv (iVFMul (z (.inr i)) (z (.inl 0))))
  constructor
  · rintro ⟨c,hc,y,⟨hy,i,hi⟩,rfl⟩
    exact ⟨⟨⟨c,hc,rfl⟩,⟨y,hy,rfl⟩⟩,i,hi⟩
  · rintro ⟨⟨⟨c,hc,he⟩,⟨y,hy,hf⟩⟩,i,hi⟩
    have hside : vfInfinitySide (c 0) (y i) := by
      change ¬ iLe (iRv iVFOne) (iRv (iVFMul (y i).val (c 0).val))
      have hyi : (y i).val = z (.inr i) := congrFun hf i
      have hc0 : (c 0).val = z (.inl 0) := congrFun he 0
      rwa [hyi,hc0]
    refine ⟨c,hc,y,⟨hy,i,hside⟩,?_⟩
    funext j
    cases j with
    | inl j => exact congrFun he j
    | inr j => exact congrFun hf j

theorem vfEscape_nonempty_of_unbounded (B : Set (Fin m → VF M))
    (hB : ¬ ∃ γ : Gamma M, ∀ y ∈ B, ∀ i, γ.val ≤ vfValue (y i))
    (c : Fin 1 → VF M) (hc : c 0 ≠ 0) : (vfEscape B c).Nonempty := by
  classical
  by_contra hno
  apply hB
  refine ⟨(finiteValue (c 0) hc)⁻¹,?_⟩
  intro y hy i
  apply le_of_not_gt
  intro hlt
  have hside : vfInfinitySide (c 0) (y i) := (vfInfinitySide_iff (c 0) (y i) hc).mpr hlt
  exact hno ⟨y,hy,i,hside⟩

end DiamondIntegral.Section2
