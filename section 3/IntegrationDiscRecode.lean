import «section 3».IntegrationDiscBases
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Definable full-code substitution for the native finite-disc charts. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {s k n : ℕ}

def integrationDiscRecode (closed : Fin k → Bool)
    (z : (Fin (s+k) ⊕ Fin (k+n)) ⊕ Fin k → M) : (Fin (s+k) × Fin 5) ⊕ Fin n → M :=
  Sum.elim (fun p => Fin.addCases
    (fun j => AdjoinGamma.embedCode ![z (.inl (.inl (Fin.castAdd k j)))] p.2)
    (fun i => integrationDiscCode (closed i) ![z (.inl (.inr (Fin.castAdd n i))),z (.inr i)] p.2) p.1)
    (fun j => z (.inl (.inr (Fin.natAdd k j))))

theorem integrationDiscRecode_definable (S : Set M) (closed : Fin k → Bool) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      ((Fin (s+k) ⊕ Fin (k+n)) ⊕ Fin k) ((Fin (s+k) × Fin 5) ⊕ Fin n) S
      (integrationDiscRecode (M := M) closed) := by
  have hg := AdjoinGamma.embedCode_definable (M := M) S
  have hd (i : Fin k) := integrationDiscCode_definable (M := M) S (closed i)
  letI := CanonicalStructure.normalize (M := M)
  intro j
  cases j with
  | inr j => exact Set.DefinableFun.proj LRV
  | inl p =>
    rcases p with ⟨i,c⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [integrationDiscRecode,Sum.elim_inl,Fin.addCases_left]
      exact (hg c).comp
        (g := fun z : (Fin (s+k) ⊕ Fin (k+n)) ⊕ Fin k → M =>
          fun _ : Fin 1 => z (.inl (.inl (Fin.castAdd k j))))
        (fun _ => Set.DefinableFun.proj LRV)
    · simp only [integrationDiscRecode,Sum.elim_inl,Fin.addCases_right]
      exact (hd j c).comp
        (g := fun z : (Fin (s+k) ⊕ Fin (k+n)) ⊕ Fin k → M =>
          ![z (.inl (.inr (Fin.castAdd n j))),z (.inr j)])
        (fun i => by fin_cases i <;> exact Set.DefinableFun.proj LRV)

def integrationDiscRecodePoint (t : Fin (s+k) → GammaParameters.Code (M := M))
    (a r : Fin k → Section2.VF M) (b : Fin n → M) :
    (Fin (s+k) ⊕ Fin (k+n)) ⊕ Fin k → M :=
  Sum.elim (Sum.elim (GammaParameters.rawTuple t)
    (Fin.append (SpecialTransformations.Section4.vfValues a) b))
    (SpecialTransformations.Section4.vfValues r)

theorem integrationDiscRecode_row (closed : Fin k → Bool)
    (R : (Fin (s+k) → ParameterPresentation.Name (M := M)) → Set (Fin n → M))
    (t : Fin (s+k) → GammaParameters.Code (M := M))
    (a r : Fin k → Section2.VF M) (hr : ∀ i, r i ≠ 0) (b : Fin n → M) :
    integrationDiscRecode closed (integrationDiscRecodePoint t a r b) ∈
      ImaginaryParameters.vectorPullback
        (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin (s+k))) R ↔
    b ∈ R (Fin.append (fun j => Sum.inr (GammaParameters.values t (Fin.castAdd k j)))
      (fun i => Sum.inl (Section2.finitePolydiscNames closed a (fun j => Section2.finiteValue (r j) (hr j)) i))) := by
  let z := integrationDiscRecode closed (integrationDiscRecodePoint t a r b)
  have hz : ∀ i : Fin (s+k), (fun j => z (.inl (i,j))) ∈ ParameterPresentation.codeDomain := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [z,integrationDiscRecode,integrationDiscRecodePoint,Sum.elim_inl,Sum.elim_inr,
        Fin.addCases_left,GammaParameters.rawTuple] using
        (AdjoinGamma.embedCode_compatible ![GammaParameters.raw (t (Fin.castAdd k j))]
          ⟨GammaParameters.raw_rv _,GammaParameters.raw_ne_zero _⟩).choose
    · simpa only [z,integrationDiscRecode,integrationDiscRecodePoint,Sum.elim_inl,Sum.elim_inr,
        Fin.addCases_right,Fin.append_left,SpecialTransformations.Section4.vfValues] using
        (integrationDiscCode_compatible (closed j) (a j) (r j) (hr j)).choose
  have hout : z ∘ Sum.inr = b := by
    funext j
    simp only [z,integrationDiscRecode,integrationDiscRecodePoint,Function.comp_apply,
      Sum.elim_inr,Sum.elim_inl,Fin.append_right]
  have hdecode (h : ∀ i : Fin (s+k), (fun j => z (.inl (i,j))) ∈ ParameterPresentation.codeDomain) :
      (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin (s+k))).decode
        ⟨z ∘ Sum.inl,h⟩ =
      Fin.append (fun j => Sum.inr (GammaParameters.values t (Fin.castAdd k j)))
        (fun i => Sum.inl (Section2.finitePolydiscNames closed a
          (fun j => Section2.finiteValue (r j) (hr j)) i)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have he := (AdjoinGamma.embedCode_compatible ![GammaParameters.raw (t (Fin.castAdd k j))]
        ⟨GammaParameters.raw_rv _,GammaParameters.raw_ne_zero _⟩).choose_spec.trans
        (congrArg Sum.inr (codeValue_raw (t (Fin.castAdd k j))))
      simpa only [z,ImaginaryParameters.tuplePresentation,integrationDiscRecode,integrationDiscRecodePoint,
        Function.comp_apply,Sum.elim_inl,Fin.addCases_left,Fin.append_left,
        ParameterPresentation.presentation,GammaParameters.rawTuple,GammaParameters.values] using he
    · simpa only [z,ImaginaryParameters.tuplePresentation,integrationDiscRecode,integrationDiscRecodePoint,
        Function.comp_apply,Sum.elim_inl,Sum.elim_inr,Fin.addCases_right,Fin.append_left,Fin.append_right,
        SpecialTransformations.Section4.vfValues,Section2.finitePolydiscNames,
        ParameterPresentation.presentation,Section2.finiteValue] using
        (integrationDiscCode_compatible (closed j) (a j) (r j) (hr j)).choose_spec
  constructor
  · rintro ⟨h,hR⟩
    change z ∘ Sum.inr ∈ R ((ImaginaryParameters.tuplePresentation
      (@ParameterPresentation.presentation M sM hM) (Fin (s+k))).decode ⟨z ∘ Sum.inl,h⟩) at hR
    rwa [hout,hdecode h] at hR
  · intro hR
    refine ⟨hz,?_⟩
    change z ∘ Sum.inr ∈ R ((ImaginaryParameters.tuplePresentation
      (@ParameterPresentation.presentation M sM hM) (Fin (s+k))).decode ⟨z ∘ Sum.inl,hz⟩)
    rwa [hout,hdecode hz]
end DiamondIntegral.Section3
