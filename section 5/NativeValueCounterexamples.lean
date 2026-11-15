import «section 5».NativeValueDistinctSyntax
import «section 5».OriginalParameterFreeFormulas
import IntegrationSection6.GammaFamilyCardinality

/-! A tuple of N+1 source rows with distinct native value patterns is an
actual original-Gamma definable counterexample, with every row guard retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

 def nativeValueCounterexamples (E : NativeRVValueSyntax M) (p a q : ℕ)
    (P : Set (Fin (p + a) → M)) : Set (Fin (p + q * a) → M) :=
  {z | (∀ i : Fin q, z ∘ familyBlockIndex p a q i ∈ P) ∧
    (valueDistinctFormula E.equal (fun (i : Fin q) (j : Fin a) => Fin.natAdd p (finProdFinEquiv (i, j)))).Realize z}

theorem nativeValueCounterexamples_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {p a : ℕ} (sp : Fin p → SortTag)
    (q : ℕ) (hq : 0 < q) (E : NativeRVValueSyntax M)
    (P : Set (Fin (p + a) → M)) (hP : DefinableOverBase B (Fin.append sp (fun _ => .rv)) P) :
    DefinableOverBase B (familyBlockSort sp (fun _ : Fin a => .rv) q) (nativeValueCounterexamples E p a q P) := by
  let st := familyBlockSort sp (fun _ : Fin a => .rv) q
  let F (i : Fin q) : Set (Fin (p + q * a) → M) :=
    {z | z ∘ familyBlockIndex p a q i ∈ P ∧ z ∈ sortedUniverse st}
  have hF (i : Fin q) : DefinableOverBase B st (F i) := hP.preimage_real st _
  have hRows := DefinableOverBase.finite_iInter Finset.univ F (fun i _ => hF i)
  have hFlags := parameter_free_formula_original_definable hc B st
    (valueDistinctFormula E.equal (fun (i : Fin q) (j : Fin a) => Fin.natAdd p (finProdFinEquiv (i, j))))
  have h := hRows.inter hFlags
  convert h using 1
  ext z
  constructor
  · rintro ⟨hr, hi⟩
    have hs : z ∈ sortedUniverse st := by
      intro j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simpa only [familyBlockIndex, Function.comp_apply, Fin.addCases_left,
          familyBlockSort, st, Fin.append_left] using
          hP.proper _ (hr ⟨0, hq⟩) (Fin.castAdd a l)
      · have hp := hP.proper _ (hr (finProdFinEquiv.symm l).1)
          (Fin.natAdd p (finProdFinEquiv.symm l).2)
        simpa only [familyBlockIndex, Function.comp_apply, Fin.addCases_right,
          Prod.mk.eta, Equiv.apply_symm_apply, familyBlockSort, st, Fin.append_right] using hp
    exact ⟨⟨hs, fun i _ => ⟨hr i, hs⟩⟩, hs, hi⟩
  · rintro ⟨⟨_, hr⟩, _, hi⟩
    exact ⟨fun i => (hr i (Finset.mem_univ _)).1, hi⟩

theorem nativeValueCounterexamples_projection_iff (B : Base (M := M)) {p a q : ℕ}
    (sp : Fin p → SortTag) (E : NativeRVValueSyntax M)
    (P : Set (Fin (p + a) → M)) (hP : DefinableOverBase B (Fin.append sp (fun _ => .rv)) P)
    (b : Fin p → M) :
    b ∈ (fun z => z ∘ Fin.castAdd (q * a)) '' nativeValueCounterexamples E p a q P ↔
      ∃ f : Fin q → (Fin a → M), (∀ i, Fin.append b (f i) ∈ P) ∧
        Function.Injective (rawRVValuePattern ∘ f) := by
  constructor
  · rintro ⟨z, ⟨hz, hflags⟩, hzb⟩
    let f (i : Fin q) (j : Fin a) := z (Fin.natAdd p (finProdFinEquiv (i, j)))
    have he (i : Fin q) : z ∘ familyBlockIndex p a q i = Fin.append b (f i) := by
      funext j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simpa only [Function.comp_apply, familyBlockIndex, Fin.addCases_left, Fin.append_left]
          using congrFun hzb l
      · simp only [Function.comp_apply, familyBlockIndex, Fin.addCases_right, Fin.append_right, f]
    have hRV (i : Fin q) (j : Fin a) : iRV (f i j) := by
      have h := hP.proper _ (hz i) (Fin.natAdd p j)
      simpa only [familyBlockIndex, Function.comp_apply, Fin.addCases_right,
        Fin.append_right, sortEval, iRV, f] using h
    refine ⟨f, (fun i => he i ▸ hz i), ?_⟩
    exact (valueDistinctFormula_realize E _ z hRV).mp hflags
  · rintro ⟨f, hf, hi⟩
    let z := Fin.append b (fun j : Fin (q * a) => f (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
    have he (i : Fin q) : z ∘ familyBlockIndex p a q i = Fin.append b (f i) := by
      funext j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simp [z, familyBlockIndex]
      · simp only [z, familyBlockIndex, Function.comp_apply, Fin.addCases_right,
          Fin.append_right, Equiv.symm_apply_apply]
    have hRV (i : Fin q) (j : Fin a) : iRV (z (Fin.natAdd p (finProdFinEquiv (i, j)))) := by
      have h := hP.proper _ (hf i) (Fin.natAdd p j)
      simpa only [z, Fin.append_right, Equiv.symm_apply_apply, Fin.append_right, sortEval, iRV] using h
    refine ⟨z, ⟨(fun i => (he i).symm ▸ hf i), ?_⟩, ?_⟩
    · apply (valueDistinctFormula_realize E _ z hRV).mpr
      simpa only [z, Function.comp_def, Fin.append_right, Equiv.symm_apply_apply, Prod.mk.eta] using hi
    · funext i
      exact Fin.append_left b _ i

end DiamondIntegral.Section5
