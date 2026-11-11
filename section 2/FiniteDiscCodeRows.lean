import «section 2».FiniteDiscCodeEquality
import «section 2».DiscTupleParameters
import Section3.GammaRVSeparation

/-! Semantic bridges for all proper finite disc presentations. The
entire invariant row is used, including every code of each Gamma value. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped Classical

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem finiteDiscRawCentres_values (q : Fin (n+n) → M) (hq : finiteDiscRawProper q) :
    vfValues (finiteDiscRawCentres q) = q ∘ Fin.castAdd n := by
  funext i
  simp only [vfValues,finiteDiscRawCentres,dite_eq_left (hq.1 i),Function.comp_apply]

theorem finiteDiscRawProper_append (a : Fin n → VF M) (c : Fin n → M) (hc : GammaParameters.Proper c) :
    finiteDiscRawProper (Fin.append (vfValues a) c) := by
  constructor
  · intro i
    simpa only [Fin.append_left,vfValues] using (a i).property
  · intro i
    simp only [Fin.append_right]
    exact ⟨(hc i).1,(hc i).2⟩

theorem finiteDiscRawNames_append (closed : Fin n → Bool) (a : Fin n → VF M)
    (c : Fin n → M) (hc : GammaParameters.Proper c) :
    finiteDiscRawNames closed (Fin.append (vfValues a) c) =
      finitePolydiscNames closed a (fun i => GammaParameters.codeValue (c i)) := by
  have ha : finiteDiscRawCentres (Fin.append (vfValues a) c) = a := by
    apply vfValues_injective
    rw [finiteDiscRawCentres_values _ (finiteDiscRawProper_append a c hc)]
    funext i
    exact Fin.append_left _ _ i
  unfold finiteDiscRawNames
  rw [ha]
  congr 1
  funext i
  simp only [Fin.append_right]

theorem raw_gamma_values_ofRaw {k : ℕ} (c : Fin k → M) (hc : GammaParameters.Proper c) :
    GammaParameters.values (GammaParameters.ofRaw c hc) = fun i => GammaParameters.codeValue (c i) := by
  funext i
  have h := GammaParameters.codeValue_raw (GammaParameters.ofRaw c hc i)
  exact h.symm

theorem finiteDiscRawNames_gamma_codes (closed : Fin n → Bool) (a : Fin n → VF M)
    (t : Fin n → GammaParameters.Code (M := M)) :
    finiteDiscRawNames closed (Fin.append (vfValues a) (GammaParameters.rawTuple t)) =
      finitePolydiscNames closed a (GammaParameters.values t) := by
  rw [finiteDiscRawNames_append closed a _ (GammaParameters.rawTuple_proper t)]
  congr 1
  funext i
  exact GammaParameters.codeValue_raw (t i)

theorem finiteDiscRawEq_congr_left (closed : Fin n → Bool) (q r s : Fin (n+n) → M)
    (hq : finiteDiscRawProper q) (hr : finiteDiscRawProper r)
    (he : finiteDiscRawNames closed q = finiteDiscRawNames closed r) :
    finiteDiscRawEq closed q s ↔ finiteDiscRawEq closed r s := by
  by_cases hs : finiteDiscRawProper s
  · rw [finiteDiscRawEq_iff closed q s hq hs,finiteDiscRawEq_iff closed r s hr hs,he]
  · exact ⟨fun h => (hs h.2.1).elim,fun h => (hs h.2.1).elim⟩

theorem FiniteDiscTupleRelation.raw_row_iff {B : ParameterBase M} {m : ℕ}
    {closed : Fin n → Bool} {sn : Fin m → SortTag} (R : FiniteDiscTupleRelation B closed sn)
    (c : Fin (R.supportArity+n) → M) (hc : GammaParameters.Proper c)
    (hσ : ∀ i, GammaParameters.codeValue (c (Fin.castAdd n i)) = R.support i)
    (q : Fin (n+n) → M) (hq : finiteDiscRawProper q)
    (hqr : q ∘ Fin.natAdd n = c ∘ Fin.natAdd R.supportArity) (x : Fin m → M) :
    (c,Fin.append (q ∘ Fin.castAdd n) x) ∈ R.relation.carrier ↔
      x ∈ R.fibre (finiteDiscRawCentres q) (fun i => GammaParameters.codeValue (q (Fin.natAdd n i))) := by
  have hv : GammaParameters.values (GammaParameters.ofRaw c hc) =
      Fin.append R.support (fun i => GammaParameters.codeValue (q (Fin.natAdd n i))) := by
    rw [raw_gamma_values_ofRaw]
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Fin.append_left] using hσ i
    · simp only [Fin.append_right]
      exact congrArg GammaParameters.codeValue (congrFun hqr i).symm
  rw [← GammaParameters.rawTuple_ofRaw c hc]
  rw [← R.relation.mem_fibre_iff _ _ hv]
  rw [← finiteDiscRawCentres_values q hq]
  rfl

end DiamondIntegral.Section2
