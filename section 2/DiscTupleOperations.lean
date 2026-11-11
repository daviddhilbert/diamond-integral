import «section 2».DiscTupleLogic
import Section8.GammaRadiusBase

/-! Uniform first-order set operations on DC-definable fibres retain all
presentations of the old names. The operation is applied before specializing
any centre or radius. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def FiniteDiscTupleRelation.rawOperation
    (hc : CanonicalStructure.IsCanonical (M := M))
    {B : ParameterBase M} {k n m : ℕ} {closed : Fin k → Bool} {sn : Fin n → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) (sm : Fin m → SortTag)
    (Φ : Set (Fin n → M) → Set (Fin m → M))
    (hΦ : ∀ {α : Type} [Finite α] (F : (α → M) → Set (Fin n → M)),
      B.real.Definable LRV {z : α ⊕ Fin n → M | z ∘ Sum.inr ∈ F (z ∘ Sum.inl)} →
      B.real.Definable LRV {z : α ⊕ Fin m → M | z ∘ Sum.inr ∈ Φ (F (z ∘ Sum.inl))}) :
    FiniteDiscTupleRelation B closed sm where
  supportArity := R.supportArity
  support := R.support
  support_mem := R.support_mem
  relation := {
    carrier := {p | GammaParameters.Proper p.1 ∧
      p.2 ∈ GammaParameters.sortedUniverse (Fin.append (fun _ : Fin k => .vf) sm) ∧
      p.2 ∘ Fin.natAdd k ∈ Φ {x | (p.1, Fin.append (p.2 ∘ Fin.castAdd m) x) ∈ R.relation.carrier}}
    definable := by
      let α := Fin (R.supportArity+k) ⊕ Fin k
      let F (p : α → M) : Set (Fin n → M) :=
        {x | (p ∘ Sum.inl, Fin.append (p ∘ Sum.inr) x) ∈ R.relation.carrier}
      have hR := R.relation.definable
      rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc] at hR
      have hF : B.real.Definable LRV {z : α ⊕ Fin n → M | z ∘ Sum.inr ∈ F (z ∘ Sum.inl)} := by
        convert hR.preimage_comp (Sum.elim (Sum.inl ∘ Sum.inl)
          (Fin.addCases (Sum.inl ∘ Sum.inr) Sum.inr)) using 1
        ext z
        change (_, Fin.append _ _) ∈ R.relation.carrier ↔ (_, _) ∈ R.relation.carrier
        have he : Fin.append ((z ∘ Sum.inl) ∘ Sum.inr) (z ∘ Sum.inr) =
            (fun j => z (Fin.addCases (Sum.inl ∘ Sum.inr) Sum.inr j)) := by
          funext j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) j
          · simp only [Fin.append_left,Function.comp_apply,Fin.addCases_left]
          · simp only [Fin.append_right,Function.comp_apply,Fin.addCases_right]
        rw [he]
        rfl
      let idx : α ⊕ Fin m → Fin (R.supportArity+k) ⊕ Fin (k+m) :=
        Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Fin.castAdd m)) (Sum.inr ∘ Fin.natAdd k)
      have hOp := (hΦ F hF).preimage_comp idx
      have hsort := (GammaParameters.sortedUniverse_definable B.real
        (Fin.append (fun _ : Fin k => .vf) sm)).raw_definable.preimage_comp
        (Sum.inr : Fin (k+m) → Fin (R.supportArity+k) ⊕ Fin (k+m))
      have hp := GammaParameters.proper_normalized_definable (M := M) B.real (n := R.supportArity+k)
      rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc] at hp
      have hproper := hp.preimage_comp
        (Sum.inl : Fin (R.supportArity+k) → Fin (R.supportArity+k) ⊕ Fin (k+m))
      rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc]
      convert hproper.inter (hsort.inter hOp) using 1
      ext z
      simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,F,idx,Function.comp_def,
        Sum.elim_inl,Sum.elim_inr]
    proper := fun _ hp => ⟨hp.1,hp.2.1⟩
    invariant := by
      intro t u he z
      have hF : {x | (GammaParameters.rawTuple t,Fin.append (z ∘ Fin.castAdd m) x) ∈ R.relation.carrier} =
          {x | (GammaParameters.rawTuple u,Fin.append (z ∘ Fin.castAdd m) x) ∈ R.relation.carrier} :=
        Set.ext (fun x => R.relation.invariant t u he _)
      change (GammaParameters.Proper (GammaParameters.rawTuple t) ∧
        z ∈ GammaParameters.sortedUniverse _ ∧ z ∘ Fin.natAdd k ∈ Φ _) ↔
        (GammaParameters.Proper (GammaParameters.rawTuple u) ∧
        z ∈ GammaParameters.sortedUniverse _ ∧ z ∘ Fin.natAdd k ∈ Φ _)
      simp only [GammaParameters.rawTuple_proper,true_and,hF] }
  invariant := by
    intro a a' δ δ' he x
    have hF := R.fibre_eq_of_names a a' δ δ' he
    have hsort (b : Fin k → VF M) :
        Fin.append (vfValues b) x ∈ GammaParameters.sortedUniverse (Fin.append (fun _ : Fin k => .vf) sm) ↔
          x ∈ GammaParameters.sortedUniverse sm := by
      constructor
      · intro h j
        simpa only [Fin.append_right] using h (Fin.natAdd k j)
      · intro h j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simpa only [Fin.append_left,vfValues,sortEval,iVF] using (b i).property
        · simpa only [Fin.append_right] using h i
    change (GammaParameters.Proper _ ∧ _ ∧ _ ∈ Φ _) ↔
      (GammaParameters.Proper _ ∧ _ ∧ _ ∈ Φ _)
    simp only [GammaParameters.rawTuple_proper,true_and,hsort,Function.comp_def,Fin.append_right,Fin.append_left]
    exact and_congr Iff.rfl (Set.ext_iff.mp (congrArg Φ hF) x)

theorem FiniteDiscTupleRelation.rawOperation_fibre
    (hc : CanonicalStructure.IsCanonical (M := M))
    {B : ParameterBase M} {k n m : ℕ} {closed : Fin k → Bool} {sn : Fin n → SortTag}
    (R : FiniteDiscTupleRelation B closed sn) (sm : Fin m → SortTag)
    (Φ : Set (Fin n → M) → Set (Fin m → M))
    (hΦ : ∀ {α : Type} [Finite α] (F : (α → M) → Set (Fin n → M)),
      B.real.Definable LRV {z : α ⊕ Fin n → M | z ∘ Sum.inr ∈ F (z ∘ Sum.inl)} →
      B.real.Definable LRV {z : α ⊕ Fin m → M | z ∘ Sum.inr ∈ Φ (F (z ∘ Sum.inl))})
    (a : Fin k → VF M) (δ : Fin k → Gamma M) :
    (R.rawOperation hc sm Φ hΦ).fibre a δ =
      GammaParameters.sortedUniverse sm ∩ Φ (R.fibre a δ) := by
  ext x
  change (GammaParameters.Proper _ ∧ _ ∧ _ ∈ Φ _) ↔ _
  simp only [GammaParameters.rawTuple_proper,true_and,Function.comp_def,Fin.append_right,Fin.append_left]
  constructor
  · rintro ⟨hs,hx⟩
    exact ⟨fun j => by simpa only [Fin.append_right] using hs (Fin.natAdd k j),hx⟩
  · rintro ⟨hs,hx⟩
    refine ⟨?_,hx⟩
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Fin.append_left,vfValues,sortEval,iVF] using (a i).property
    · simpa only [Fin.append_right] using hs i

end DiamondIntegral.Section2
