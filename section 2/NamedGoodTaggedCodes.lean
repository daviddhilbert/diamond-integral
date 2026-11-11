import «section 2».DiscTupleOperations
import «section 2».ParametricTaggedPolydiscs

/-! The complete good-polydisc formula descends through every equivalent
presentation of the fixed DC ground names. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem goodTaggedCodes_definable_disc_names (hc : CanonicalStructure.IsCanonical (M := M))
    (B : ParameterBase M) {k n : ℕ} (closed : Fin k → Bool)
    (a : Fin k → VF M) (δ : Fin k → Gamma M) (F : Set ((Fin n → M) × M))
    (hF : DefinableOverFiniteDiscNames B closed a δ (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F}) :
    DefinableOverFiniteDiscNames B closed a δ (fun _ : Fin (n+n) => .vf)
      (GammaParameters.sortedUniverse (fun _ => .vf) ∩ rawGoodTaggedPolydiscCodes F) := by
  let Φ (U : Set (Fin (n+1) → M)) : Set (Fin (n+n) → M) :=
    rawGoodTaggedPolydiscCodes {p | Fin.snoc p.1 p.2 ∈ U}
  have hΦ {α : Type} [Finite α] (U : (α → M) → Set (Fin (n+1) → M))
      (hU : B.real.Definable LRV {z : α ⊕ Fin (n+1) → M | z ∘ Sum.inr ∈ U (z ∘ Sum.inl)}) :
      B.real.Definable LRV {z : α ⊕ Fin (n+n) → M | z ∘ Sum.inr ∈ Φ (U (z ∘ Sum.inl))} := by
    refine parametricGoodTaggedPolydiscCodes_definable B.real
      (fun p => {q | Fin.snoc q.1 q.2 ∈ U p}) ?_
    convert hU using 1
    ext z
    change Fin.snoc (Fin.init (z ∘ Sum.inr)) ((z ∘ Sum.inr) (Fin.last n)) ∈ U (z ∘ Sum.inl) ↔ _
    rw [Fin.snoc_init_self]
    rfl
  obtain ⟨R,hR⟩ := hF
  have hPhiF : Φ (R.fibre a δ) = rawGoodTaggedPolydiscCodes F := by
    dsimp only [Φ]
    have he : {p : (Fin n → M) × M | Fin.snoc p.1 p.2 ∈ R.fibre a δ} = F := by
      rw [hR]
      ext p
      simp only [Set.mem_ofPred_eq,Fin.init_snoc,Fin.snoc_last]
    rw [he]
  refine ⟨R.rawOperation hc (fun _ => .vf) Φ hΦ,?_⟩
  rw [FiniteDiscTupleRelation.rawOperation_fibre,hPhiF]

theorem rawOpenPolydiscProper_sorted {n : ℕ} (d : Fin (n+n) → M)
    (hd : rawOpenPolydiscProper d) :
    d ∈ GammaParameters.sortedUniverse (fun _ => .vf) := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [Matrix.cons_val_zero,sortEval,iVF] using (hd i).1 0
  · simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,sortEval,iVF] using (hd i).1 1

end DiamondIntegral.Section2
