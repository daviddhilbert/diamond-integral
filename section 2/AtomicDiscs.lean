import «section 2».Atomic
import «section 2».DiscPoints
import Section3.GammaBaseVFAlgebraicity

/-! The unary case of Lemma 2.24, using the author-approved R029 proof.
All conclusions use the original real/Gamma ground base. Additional DC
ground names and higher-dimensional induction are not silently included. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Adjoining an RV element retains it as a real RV name, rather than
discarding its residue information and retaining only its value. -/
def adjoinRV (B : ParameterBase M) (t : RVInfinity M) : ParameterBase M :=
  ⟨insert t.val B.real, B.gamma⟩

omit [LRV.Structure M] hM in
private theorem unary_eta (z : Fin 1 → M) : (fun _ : Fin 1 => z 0) = z := by
  funext i
  fin_cases i
  rfl

/-- The unary case of Lemma 2.24. The argument works for any infinite
atomic valuative disc, so proper openness is not needed as an extra premise.
The RV parameter may even be rv(0). No nontrivial-ground-value-group
assumption or atomic-base-change input from Lemma 2.23 is used. -/
theorem lemma_2_24_unary (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M)
    (D : Set M) (hball : IsBall D) (hinf : D.Infinite)
    (hA : IsAtomic B (fun _ : Fin 1 => .vf) {z | z 0 ∈ D})
    (t : RVInfinity M) :
    IsAtomic (adjoinRV B t) (fun _ : Fin 1 => .vf) {z | z 0 ∈ D} := by
  let E := adjoinRV B t
  have hBD : GammaParameters.DefinableAtBase E .vf D :=
    hA.1.mono (Set.subset_insert _ _) (Set.Subset.refl _)
  have hInf : ({z : Fin 1 → M | z 0 ∈ D} : Set (Fin 1 → M)).Infinite := by
    intro hf
    apply hinf
    apply (hf.image (fun z => z 0)).subset
    intro x hx
    exact ⟨fun _ => x, hx, rfl⟩
  refine ⟨hBD, hA.2.1, hA.2.2.1, ?_⟩
  intro C hC
  let C₀ : Set M := {x | (fun _ : Fin 1 => x) ∈ C}
  have hC₀ : GammaParameters.DefinableAtBase E .vf C₀ := by
    change GammaParameters.DefinableOverBase E (fun _ : Fin 1 => .vf)
      {z | (fun _ : Fin 1 => z 0) ∈ C}
    simpa only [unary_eta, Set.ofPred_mem_eq] using hC
  by_cases hsub : D ⊆ C₀
  · left
    intro z hz
    have h := hsub hz
    change (fun _ : Fin 1 => z 0) ∈ C at h
    rwa [unary_eta] at h
  by_cases hdis : Disjoint D C₀
  · right
    apply Set.disjoint_left.mpr
    intro z hz hzC
    apply Set.disjoint_left.mp hdis hz
    change (fun _ : Fin 1 => z 0) ∈ C
    rwa [unary_eta]
  have hne : (C₀ ∩ D).Nonempty := by
    obtain ⟨x, hxD, hxC⟩ := Set.not_disjoint_iff.mp hdis
    exact ⟨x, hxC, hxD⟩
  have hproper : C₀ ∩ D ⊂ D := by
    refine ⟨Set.inter_subset_right, ?_⟩
    intro hback
    exact hsub (fun x hx => (hback hx).1)
  obtain ⟨x, hxD, hxdef⟩ := lemma_2_21 h00 E C₀ D hC₀ hBD hball hne hproper
  let b : VF M := ⟨x, hxdef.proper x rfl⟩
  have hxb : GammaParameters.AlgebraicAtBase E .vf b.val :=
    ⟨{x}, hxdef, Set.finite_singleton x, Set.mem_singleton x⟩
  have hxraw : AlgebraicAt (B.real ∪ {t.val}) .vf b.val := by
    simpa only [Set.union_singleton, E, adjoinRV] using
      (GammaParameters.algebraic_vf_iff_real E b).mp hxb
  have ht : ∀ s ∈ ({t.val} : Set M), iRV s := by
    intro s hs
    rw [Set.mem_singleton_iff.mp hs]
    exact t.property
  have hxbase : GammaParameters.AlgebraicAtBase B .vf x :=
    (GammaParameters.algebraic_vf_iff_real B b).mpr
      ((algebraicAt_vf_union_rv_iff B.real {t.val} ht b).mp hxraw)
  exact (hA.not_algebraic_at hInf (a := fun _ => x) hxD hxbase).elim

end DiamondIntegral.Section2
