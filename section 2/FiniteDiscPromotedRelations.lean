import «section 2».FiniteDiscHullInvariance
import Section8.GammaRadiusBase

/-! A promoted relation over the original real base, with both Gamma
and DC invariance restored globally. No centre is a ground parameter. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k n p m : ℕ}

theorem discHullCurrent_proper (c : Fin (k+n) → M) (hc : GammaParameters.Proper c)
    (z : Fin (n+(p+m)) → M) (hz : ∀ i, iVF (z (Fin.castAdd (p+m) i))) :
    finiteDiscRawProper (discHullCurrent c z) := by
  constructor
  · intro i
    simpa only [discHullCurrent,Fin.append_left,Function.comp_apply] using hz i
  · intro i
    simp only [discHullCurrent,Fin.append_right,Function.comp_apply]
    exact ⟨(hc (Fin.natAdd k i)).1,(hc (Fin.natAdd k i)).2⟩

theorem discHullCurrent_names (closed : Fin n → Bool) (c : Fin (k+n) → M)
    (hc : GammaParameters.Proper c) (a : Fin n → VF M) (x : Fin (p+m) → M)
    (δ : Fin n → Gamma M) (hδ : ∀ i, GammaParameters.codeValue (c (Fin.natAdd k i)) = δ i) :
    finiteDiscRawNames closed (discHullCurrent c (Fin.append (vfValues a) x)) =
      finitePolydiscNames closed a δ := by
  rw [discHullCurrent_append,finiteDiscRawNames_append]
  · congr 1
    funext i
    exact hδ i
  · exact fun i => hc (Fin.natAdd k i)

theorem discHullCurrent_same_values (closed : Fin n → Bool) (c d : Fin (k+n) → M)
    (hc : GammaParameters.Proper c) (hd : GammaParameters.Proper d)
    (z : Fin (n+(p+m)) → M) (hz : ∀ i, iVF (z (Fin.castAdd (p+m) i)))
    (he : ∀ j, GammaParameters.codeValue (c j) = GammaParameters.codeValue (d j)) :
    finiteDiscRawEq closed (discHullCurrent c z) (discHullCurrent d z) := by
  apply (finiteDiscRawEq_iff closed _ _ (discHullCurrent_proper c hc z hz) (discHullCurrent_proper d hd z hz)).mpr
  let a : Fin n → VF M := fun i => ⟨z (Fin.castAdd (p+m) i),hz i⟩
  change finiteDiscRawNames closed (Fin.append (vfValues a) (c ∘ Fin.natAdd k)) =
    finiteDiscRawNames closed (Fin.append (vfValues a) (d ∘ Fin.natAdd k))
  calc
    _ = finitePolydiscNames closed a (fun i => GammaParameters.codeValue (c (Fin.natAdd k i))) :=
      finiteDiscRawNames_append closed a _ (fun i => hc (Fin.natAdd k i))
    _ = finitePolydiscNames closed a (fun i => GammaParameters.codeValue (d (Fin.natAdd k i))) := by
      congr 1
      funext i
      exact he (Fin.natAdd k i)
    _ = _ := (finiteDiscRawNames_append closed a _ (fun i => hd (Fin.natAdd k i))).symm

def discPromotedGammaRelation (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (closed : Fin n → Bool) (sp : Fin p → SortTag) (sn : Fin m → SortTag)
    (H : Set (Fin p ⊕ (Fin (k+n) ⊕ Fin (n+m)) → M)) (hHd : S.Definable LRV H)
    (hHi : ∀ v b (t u : Fin (k+n) → GammaParameters.Code (M := M)),
      GammaParameters.values t = GammaParameters.values u →
      (Sum.elim v (Sum.elim (GammaParameters.rawTuple t) b) ∈ H ↔
        Sum.elim v (Sum.elim (GammaParameters.rawTuple u) b) ∈ H)) :
    GammaParameters.Relation S (k+n) (n+(p+m)) (Fin.append (fun _ : Fin n => .vf) (Fin.append sp sn)) where
  carrier := {q | GammaParameters.Proper q.1 ∧
    q.2 ∈ GammaParameters.sortedUniverse (Fin.append (fun _ : Fin n => .vf) (Fin.append sp sn)) ∧
    discInvariantHull closed H q.1 q.2}
  definable := by
    rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc]
    have hp := (GammaParameters.proper_normalized_definable (M := M) S (n := k+n))
    rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc] at hp
    have hs := ((definableOver_iff_normalized_raw S _ _).mp
      (GammaParameters.sortedUniverse_definable S (Fin.append (fun _ : Fin n => .vf) (Fin.append sp sn)))).1
    rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc] at hs
    exact (hp.preimage_comp (Sum.inl : Fin (k+n) → Fin (k+n) ⊕ Fin (n+(p+m)))).inter
      ((hs.preimage_comp Sum.inr).inter (discInvariantHull_definable S closed H hHd))
  proper := fun _ h => ⟨h.1,h.2.1⟩
  invariant := by
    intro t u he z
    by_cases hz : z ∈ GammaParameters.sortedUniverse (Fin.append (fun _ : Fin n => .vf) (Fin.append sp sn))
    · have hzVF : ∀ i, iVF (z (Fin.castAdd (p+m) i)) := by
        intro i
        simpa only [Fin.append_left,sortEval,iVF] using hz (Fin.castAdd (p+m) i)
      have hv : ∀ j, GammaParameters.codeValue (GammaParameters.rawTuple t j) =
          GammaParameters.codeValue (GammaParameters.rawTuple u j) := by
        intro j
        change GammaParameters.codeValue (GammaParameters.raw (t j)) = GammaParameters.codeValue (GammaParameters.raw (u j))
        rw [GammaParameters.codeValue_raw,GammaParameters.codeValue_raw]
        exact congrFun he j
      change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
      simp only [GammaParameters.rawTuple_proper,hz,true_and]
      exact discInvariantHull_congr closed H hHi _ _ (GammaParameters.rawTuple_proper t)
        (GammaParameters.rawTuple_proper u) z z
        (discHullCurrent_same_values closed _ _ (GammaParameters.rawTuple_proper t)
          (GammaParameters.rawTuple_proper u) z hzVF hv) rfl (fun i => hv (Fin.castAdd n i))
    · exact ⟨fun h => (hz h.2.1).elim,fun h => (hz h.2.1).elim⟩

end DiamondIntegral.Section2
