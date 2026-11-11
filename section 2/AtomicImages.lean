import «section 2».AtomicPolydiscs

/-! Constancy of a definable RV-image relation on an atomic polydisc.
The full image relation is used; no RV branch labels are discarded. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Fixing an RV output uses its full RV name, including the zero tag. -/
theorem rv_row_definable (B : ParameterBase M) {n : ℕ}
    (R : Set ((Fin n → M) × M))
    (hR : GammaParameters.DefinableOverBase B
      (Fin.lastCases .rv (fun _ : Fin n => .vf))
      {z | (Fin.init z, z (Fin.last n)) ∈ R}) (t : RVInfinity M) :
    GammaParameters.DefinableOverBase (adjoinRV B t) (fun _ : Fin n => .vf)
      {a | (a, t.val) ∈ R} := by
  let E := adjoinRV B t
  let sn : Fin (n + 1) → SortTag := Fin.lastCases .rv (fun _ => .vf)
  have hR' : GammaParameters.DefinableOverBase E sn
      {z | (Fin.init z, z (Fin.last n)) ∈ R} :=
    hR.mono (show B.real ⊆ E.real from Set.subset_insert _ _) (Set.Subset.refl _)
  have ht : GammaParameters.DefinableClosureAtBase E .rv t.val :=
    GammaParameters.real_definableAtBase E .rv {t.val}
      (definableClosureAt_of_mem (Set.mem_insert _ _) t.property)
  have hname := ht.preimage_real sn (fun _ : Fin 1 => Fin.last n)
  have hp := (hR'.inter hname).image_real Fin.castSucc
  have hst : sn ∘ Fin.castSucc = (fun _ : Fin n => .vf) := by
    funext j
    simp only [sn, Function.comp_apply, Fin.lastCases_castSucc]
  rw [hst] at hp
  convert hp using 1
  ext a
  constructor
  · intro ha
    let w : Fin (n + 1) → M := Fin.snoc a t.val
    have hwR : (Fin.init w, w (Fin.last n)) ∈ R := by
      simpa only [w, Fin.init_snoc, Fin.snoc_last, Set.mem_ofPred_eq] using ha
    have hws := hR'.proper w hwR
    refine ⟨w, ⟨hwR, ?_⟩, ?_⟩
    · exact ⟨by simp [w], hws⟩
    · funext j
      simp only [w, Function.comp_apply, Fin.snoc_castSucc]
  · rintro ⟨w, ⟨hwR, hwt, _⟩, he⟩
    have hwa : Fin.init w = a := he
    have hwl : w (Fin.last n) = t.val := hwt
    change (Fin.init w, w (Fin.last n)) ∈ R at hwR
    change (a, t.val) ∈ R
    rwa [hwa, hwl] at hwR

/-- The RV-relation form of Lemma 2.26. For the paper's finitary map,
R is its complete RV-image relation. The constancy argument itself needs
neither finiteness nor injectivity of RV on the VF-valued fibres. -/
theorem lemma_2_26_rv_relation (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M)
    {n : ℕ} (D : Fin n → Set M) (hball : ∀ j, IsBall (D j))
    (hinf : ∀ j, (D j).Infinite)
    (hA : IsAtomic B (fun _ => .vf) {a | ∀ j, a j ∈ D j})
    (R : Set ((Fin n → M) × M))
    (hR : GammaParameters.DefinableOverBase B
      (Fin.lastCases .rv (fun _ : Fin n => .vf))
      {z | (Fin.init z, z (Fin.last n)) ∈ R}) :
    ∀ a ∈ {z | ∀ j, z j ∈ D j}, ∀ a' ∈ {z | ∀ j, z j ∈ D j},
      {t | (a, t) ∈ R} = {t | (a', t) ∈ R} := by
  have hmem (a a' : Fin n → M) (ha : ∀ j, a j ∈ D j) (ha' : ∀ j, a' j ∈ D j)
      (x : M) (hx : (a, x) ∈ R) : (a', x) ∈ R := by
    have hRa : (Fin.snoc a x : Fin (n + 1) → M) ∈ {z : Fin (n + 1) → M | (Fin.init z, z (Fin.last n)) ∈ R} := by
      simpa only [Fin.init_snoc, Fin.snoc_last, Set.mem_ofPred_eq] using hx
    have hxsort := hR.proper (Fin.snoc a x : Fin (n + 1) → M) hRa (Fin.last n)
    have hxRV : iRV x := by
      simpa only [Fin.lastCases_last, Fin.snoc_last, sortEval, iRV] using hxsort
    let t : RVInfinity M := ⟨x, hxRV⟩
    have hAtomic := lemma_2_24 h00 B D hball hinf hA t
    have hCut := rv_row_definable B R hR t
    rcases hAtomic.2.2.2 {a | (a, t.val) ∈ R} hCut with hsub | hdis
    · exact hsub ha'
    · exact (Set.disjoint_left.mp hdis ha hx).elim
  intro a ha a' ha'
  ext x
  exact ⟨hmem a a' ha ha' x, hmem a' a ha' ha x⟩

end DiamondIntegral.Section2
