import «section 6».FocusCovarianceParameterLoci

/-! The first-order focus covariance test is exactly covariance on
the actual erased VF tuples and the actual coefficient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S T : Set M} {n r : ℕ}
variable {ι : Type} [Finite ι]

theorem congruent_erased_iff (β : Gamma M) (j : Fin n) (a b : Fin n → VF M) :
    Congruent (fun _ => β) (Function.update a j 0) (Function.update b j 0) ↔
      ∀ i,i ≠ j → β.val < vfValue (a i-b i) := by
  constructor
  · intro h i hi
    simpa only [Function.update_of_ne hi] using h i
  · intro h i
    by_cases hi : i=j
    · subst i
      simp only [Function.update_self,sub_self]
      exact gamma_lt_value_zero β
    · simpa only [Function.update_of_ne hi] using h i hi

theorem focusCovarianceCodeCondition_at (a : ι → M) (c : VF M)
    (t : RVInfinity M) (ht : t ≠ rvZero M) (j : Fin n)
    (p q : Mixed M n r) (f g : VF M) :
    Sum.elim (Sum.elim (Sum.elim a (fun _ : Fin 1 => c.val)) (fun _ : Fin 1 => t.val))
      (Sum.elim (Sum.elim (mixedValues p) (fun _ : Fin 1 => f.val))
        (Sum.elim (mixedValues q) (fun _ : Fin 1 => g.val))) ∈ focusCovarianceCodeCondition ι j ↔
      (p.2=q.2 → Congruent (fun _ => GammaParameters.codeValue t.val)
        (Function.update p.1 j 0) (Function.update q.1 j 0) →
          vfValue (c*f)<vfValue (f-g)) := by
  have hTag : (∀ k : Fin r,(p.2 k).val=(q.2 k).val) ↔ p.2=q.2 :=
    ⟨fun h => funext (fun k => Subtype.ext (h k)),fun h k => congrArg (fun u => (u k).val) h⟩
  have hClose : (∀ i : Fin n,i ≠ j → ¬ iLe (rv M (p.1 i-q.1 i)).val t.val) ↔
      Congruent (fun _ => GammaParameters.codeValue t.val) (Function.update p.1 j 0) (Function.update q.1 j 0) := by
    rw [congruent_erased_iff]
    apply forall_congr'
    intro i
    apply imp_congr_right
    intro _
    rw [← Values.vrv_le_iff,not_le,nonzero_rv_codeValue_val t ht]
    rfl
  have hOut : (¬ iLe (rv M (f-g)).val (rv M (c*f)).val) ↔ vfValue (c*f)<vfValue (f-g) := by
    rw [← Values.vrv_le_iff,not_le]
    rfl
  change ((∀ k : Fin r,(p.2 k).val=(q.2 k).val) →
    (∀ i : Fin n,i ≠ j → ¬ iLe (rv M (p.1 i-q.1 i)).val t.val) →
      ¬ iLe (rv M (f-g)).val (rv M (c*f)).val) ↔ _
  rw [hTag,hClose,hOut]

theorem mem_focusErasedCovarianceParameterLocus_map_iff
    (R : Set (ι ⊕ FocusEntryIndex n r → M)) (a : ι → M) (c : VF M)
    (t : RVInfinity M) (ht : t ≠ rvZero M) (j : Fin n)
    {A : DefSet (rawMixedSpace (M := M) n r) T}
    (f : Map A (DefSet.univ (rawVFSpace (M := M) 1) T))
    (hSection : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawVFSpace 1) f.graph) :
    Sum.elim (Sum.elim a (fun _ : Fin 1 => c.val)) (fun _ : Fin 1 => t.val) ∈
      focusErasedCovarianceParameterLocus R j ↔
      ∀ p q : A,p.val.2=q.val.2 →
        Congruent (fun _ => GammaParameters.codeValue t.val) (Function.update p.val.1 j 0) (Function.update q.val.1 j 0) →
          vfValue (c*(f p).val 0)<vfValue ((f p).val 0-(f q).val 0) := by
  let parameterCode : FocusMetadataIndex ι → M := Sum.elim (Sum.elim a (fun _ : Fin 1 => c.val)) (fun _ : Fin 1 => t.val)
  have hAt (z) : Sum.elim parameterCode z ∈ focusGraphWithMetadata R ↔
      ∃ p : A,Sum.elim (mixedValues p.val) (vfValues (f p).val)=z :=
    (Set.ext_iff.mp hSection z).trans (scalarMapGraph_iff f z)
  have hScalar (p : A) : vfValues (f p).val=(fun _ : Fin 1 => ((f p).val 0).val) := by
    funext i; fin_cases i; rfl
  constructor
  · intro h p q hRV hClose
    have hp := (hAt _).mpr ⟨p,rfl⟩
    have hq := (hAt _).mpr ⟨q,rfl⟩
    have hRaw := h _ _ hp hq
    rw [hScalar p,hScalar q] at hRaw
    exact (focusCovarianceCodeCondition_at a c t ht j p.val q.val ((f p).val 0) ((f q).val 0)).mp
      hRaw hRV hClose
  · intro h x y hx hy
    obtain ⟨p,rfl⟩ := (hAt x).mp hx
    obtain ⟨q,rfl⟩ := (hAt y).mp hy
    change Sum.elim parameterCode (Sum.elim (Sum.elim (mixedValues p.val) (vfValues (f p).val))
      (Sum.elim (mixedValues q.val) (vfValues (f q).val))) ∈ focusCovarianceCodeCondition ι j
    rw [hScalar p,hScalar q]
    exact (focusCovarianceCodeCondition_at a c t ht j p.val q.val ((f p).val 0) ((f q).val 0)).mpr (h p q)

end DiamondIntegral.Section6
