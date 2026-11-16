import «section 6».FocusSourceParameterLoci
import «section 6».FocusCovarianceCodeSemantics

/-! The first-order source test is exactly the pointwise anisotropic
invariance condition needed to reconstruct permitted focus components. -/

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

theorem focusSourceCodeCondition_at
    (A : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) (a : ι → M)
    {B : DefSet (rawMixedSpace (M := M) n r) T}
    (hSection : {z | Sum.elim a z ∈ A}=(rawMixedSpace n r).preimage B.carrier)
    (c : VF M) (t : RVInfinity M) (ht : t ≠ rvZero M) (j : Fin n)
    (p : Mixed M n r) (f : VF M) (b : Fin n → VF M) :
    Sum.elim (Sum.elim (Sum.elim a (fun _ : Fin 1 => c.val)) (fun _ : Fin 1 => t.val))
      (Sum.elim (Sum.elim (mixedValues p) (fun _ : Fin 1 => f.val)) (vfValues b)) ∈
        focusSourceCodeCondition A j ↔
      ((∀ i,(if i=j then vfValue (c*f) else (GammaParameters.codeValue t.val).val)<vfValue (p.1 i-b i)) →
        (b,p.2) ∈ B.carrier) := by
  have hTarget : Sum.elim a (mixedValues (b,p.2)) ∈ A ↔ (b,p.2) ∈ B.carrier := by
    have h := (rawMixedSpace (M := M) n r).preimage_decode B.carrier
      ⟨mixedValues (b,p.2),mixedValues_mem_domain _⟩
    rw [decode_mixedValues] at h
    exact (Set.ext_iff.mp hSection _).trans h
  have hClose : (∀ i : Fin n,¬ iLe (rv M (p.1 i-b i)).val
      (if i=j then (rv M (c*f)).val else t.val)) ↔
      ∀ i : Fin n,(if i=j then vfValue (c*f) else (GammaParameters.codeValue t.val).val)<vfValue (p.1 i-b i) := by
    apply forall_congr'
    intro i
    by_cases hi : i=j
    · simp only [if_pos hi]
      rw [← Values.vrv_le_iff,not_le]
      rfl
    · simp only [if_neg hi]
      rw [← Values.vrv_le_iff,not_le,nonzero_rv_codeValue_val t ht]
      rfl
  have hVF : ∀ i : Fin n,iVF (b i).val := fun i => (b i).property
  change ((∀ i : Fin n,iVF (b i).val) →
    (∀ i : Fin n,¬ iLe (rv M (p.1 i-b i)).val (if i=j then (rv M (c*f)).val else t.val)) →
      Sum.elim a (mixedValues (b,p.2)) ∈ A) ↔ _
  simp only [hVF,forall_const,true_implies,hClose,hTarget]

theorem mem_focusSourceInvariantParameterLocus_map_iff
    (A : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) (R : Set (ι ⊕ FocusEntryIndex n r → M))
    (a : ι → M) (c : VF M) (t : RVInfinity M) (ht : t ≠ rvZero M) (j : Fin n)
    {B C : DefSet (rawMixedSpace (M := M) n r) T}
    (f : Map C (DefSet.univ (rawVFSpace (M := M) 1) T))
    (hSource : {z | Sum.elim a z ∈ A}=(rawMixedSpace n r).preimage B.carrier)
    (hGraph : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawVFSpace 1) f.graph) :
    Sum.elim (Sum.elim a (fun _ : Fin 1 => c.val)) (fun _ : Fin 1 => t.val) ∈
      focusSourceInvariantParameterLocus A R j ↔
      ∀ p : C,∀ b : Fin n → VF M,
        (∀ i,(if i=j then vfValue (c*(f p).val 0) else (GammaParameters.codeValue t.val).val)<
          vfValue (p.val.1 i-b i)) → (b,p.val.2) ∈ B.carrier := by
  let parameterCode : FocusMetadataIndex ι → M :=
    Sum.elim (Sum.elim a (fun _ : Fin 1 => c.val)) (fun _ : Fin 1 => t.val)
  have hAt (z) : Sum.elim parameterCode z ∈ focusGraphWithMetadata R ↔
      ∃ p : C,Sum.elim (mixedValues p.val) (vfValues (f p).val)=z :=
    (Set.ext_iff.mp hGraph z).trans (scalarMapGraph_iff f z)
  have hScalar (p : C) : vfValues (f p).val=(fun _ : Fin 1 => ((f p).val 0).val) := by
    funext i; fin_cases i; rfl
  constructor
  · intro h p b hClose
    have hRaw := h _ ((hAt _).mpr ⟨p,rfl⟩) (vfValues b)
    rw [hScalar p] at hRaw
    exact (focusSourceCodeCondition_at A a hSource c t ht j p.val ((f p).val 0) b).mp hRaw hClose
  · intro h x hx y
    obtain ⟨p,rfl⟩ := (hAt x).mp hx
    by_cases hVF : ∀ i : Fin n,iVF (y i)
    · let b : Fin n → VF M := fun i => ⟨y i,hVF i⟩
      have hRaw := (focusSourceCodeCondition_at A a hSource c t ht j p.val ((f p).val 0) b).mpr (h p b)
      have hb : vfValues b=y := by funext i; rfl
      rw [hb] at hRaw
      simpa only [← hScalar p] using hRaw
    · change (∀ i : Fin n,iVF (y i)) → _
      exact fun hy => False.elim (hVF hy)

end DiamondIntegral.Section6
