import «section 2».AtomicPolydiscs

/-!
# Complete type generation on coordinate fibres

The source need not be definable. Fixing all but one coordinate gives a
complete type over those actual fixed points. The varying coordinate is
never named. This is the fibre step in the induction for Lemma 2.25.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem GeneratesCompleteType.image_real {B : ParameterBase M} {n m : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)} (hA : GeneratesCompleteType B sn A)
    (π : Fin m → Fin n) :
    GeneratesCompleteType B (sn ∘ π) ((fun a => a ∘ π) '' A) := by
  refine ⟨hA.1.image _, ?_, ?_⟩
  · rintro x ⟨a, ha, rfl⟩ i
    exact hA.2.1 ha (π i)
  · intro C hC
    let U := {a : Fin n → M | a ∘ π ∈ C ∧ a ∈ GammaParameters.sortedUniverse sn}
    have hU : GammaParameters.DefinableOverBase B sn U := hC.preimage_real sn π
    rcases hA.2.2 U hU with hsub | hdis
    · exact Or.inl (by rintro x ⟨a, ha, rfl⟩; exact (hsub ha).1)
    · exact Or.inr (Set.disjoint_left.mpr (by
        rintro x ⟨a, ha, rfl⟩ hx
        exact Set.disjoint_left.mp hdis ha ⟨hx, hA.2.1 ha⟩))

theorem GeneratesCompleteType.coordinate_fibre {B : ParameterBase M} {n : ℕ}
    {A : Set (Fin (n+1) → M)} (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (a : Fin (n+1) → M) (ha : a ∈ A) (i : Fin (n+1)) :
    GeneratesCompleteType (tupleBase B (Fin.removeNth i a)) (fun _ : Fin 1 => .vf)
      {z | Fin.insertNth i (z 0) (Fin.removeNth i a) ∈ A} := by
  classical
  let E := tupleBase B (Fin.removeNth i a)
  refine ⟨⟨fun _ => a i, ?_⟩, ?_, ?_⟩
  · change Fin.insertNth i (a i) (Fin.removeNth i a) ∈ A
    rwa [Fin.insertNth_self_removeNth]
  · intro z hz j
    fin_cases j
    change sortEval SortTag.vf (z 0)
    have h := hA.2.1 hz i
    simpa only [Fin.insertNth_apply_same] using h
  · intro C hC
    let C₀ : Set M := {x | (fun _ : Fin 1 => x) ∈ C}
    have heta (z : Fin 1 → M) : (fun _ : Fin 1 => z 0) = z := by
      funext j
      fin_cases j
      rfl
    have hC₀ : GammaParameters.DefinableAtBase E .vf C₀ := by
      change GammaParameters.DefinableOverBase E (fun _ : Fin 1 => .vf)
        {z | (fun _ : Fin 1 => z 0) ∈ C}
      simpa only [heta, Set.ofPred_mem_eq] using hC
    have hnames (j : Fin n) : iVF (Fin.removeNth i a j) := hA.2.1 ha (i.succAbove j)
    obtain ⟨P, hP, hrow⟩ := GammaParameters.promote_scalar_definable_base B
      (fun _ : Fin n => .vf) (Fin.removeNth i a) hnames .vf C₀ hC₀
    have hst : Fin.lastCases SortTag.vf (fun _ : Fin n => .vf) =
        (fun _ : Fin (n+1) => .vf) := by
      funext j
      exact Fin.lastCases (by simp) (fun _ => by simp) j
    rw [hst] at hP
    let π : Fin (n+1) → Fin (n+1) := Fin.lastCases i i.succAbove
    have hinit (z : Fin (n+1) → M) : Fin.init (z ∘ π) = Fin.removeNth i z := by
      funext j
      simp [π, Fin.init, Fin.removeNth]
    have hlast (z : Fin (n+1) → M) : (z ∘ π) (Fin.last n) = z i := by
      simp [π]
    let U : Set (Fin (n+1) → M) := {z | (Fin.removeNth i z, z i) ∈ P ∧
      z ∈ GammaParameters.sortedUniverse (fun _ => .vf)}
    have hU : GammaParameters.DefinableOverBase B (fun _ => .vf) U := by
      have hp := hP.preimage_real (fun _ : Fin (n+1) => .vf) π
      convert hp using 1
      ext z
      change ((Fin.removeNth i z, z i) ∈ P ∧ _) ↔
        ((Fin.init (z ∘ π), (z ∘ π) (Fin.last n)) ∈ P ∧ _)
      rw [hinit, hlast]
    have hpoint (z : Fin 1 → M) :
        Fin.insertNth i (z 0) (Fin.removeNth i a) ∈ U → z ∈ C := by
      intro h
      have hp := h.1
      simp only [Fin.removeNth_insertNth, Fin.insertNth_apply_same] at hp
      have hc : (fun _ : Fin 1 => z 0) ∈ C := (Set.ext_iff.mp hrow (z 0)).mp hp
      rwa [heta] at hc
    have hpoint' (z : Fin 1 → M)
        (hz : Fin.insertNth i (z 0) (Fin.removeNth i a) ∈ A) (hc : z ∈ C) :
        Fin.insertNth i (z 0) (Fin.removeNth i a) ∈ U := by
      refine ⟨?_, hA.2.1 hz⟩
      have hc₀ : z 0 ∈ C₀ := by
        change (fun _ : Fin 1 => z 0) ∈ C
        rwa [heta]
      have hp := (Set.ext_iff.mp hrow (z 0)).mpr hc₀
      change (Fin.removeNth i a, z 0) ∈ P at hp
      simpa only [Fin.removeNth_insertNth, Fin.insertNth_apply_same] using hp
    rcases hA.2.2 U hU with hsub | hdis
    · exact Or.inl (fun z hz => hpoint z (hsub hz))
    · exact Or.inr (Set.disjoint_left.mpr (fun z hz hc =>
        Set.disjoint_left.mp hdis hz (hpoint' z hz hc)))

end DiamondIntegral.Section2
