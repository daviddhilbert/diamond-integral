import «section 6».FocusCovarianceParameterLoci

/-! Correct leading terms of an entire partial focus graph are a
first-order parameter condition, with an exact actual-map interpretation. -/

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

def focusLeadingTermParameterLocus (R : Set (ι ⊕ FocusEntryIndex n r → M)) (j : Fin n) : Set (ι → M) :=
  {a | ∀ z,Sum.elim a z ∈ R → iRv (z (.inr 0))=iRv (z (.inl (.inl j)))}

theorem focusLeadingTermParameterLocus_definable
    (R : Set (ι ⊕ FocusEntryIndex n r → M)) (hR : S.Definable LRV R) (j : Fin n) :
    S.Definable LRV (focusLeadingTermParameterLocus R j) := by
  have hEq : S.Definable LRV {z : ι ⊕ FocusEntryIndex n r → M |
      iRv (z (.inr (.inr 0)))=iRv (z (.inr (.inl (.inl j))))} :=
    (rv_scalarCode_definable (Set.DefinableFun.proj LRV)).ofPred_eq
      (rv_scalarCode_definable (Set.DefinableFun.proj LRV))
  convert ((hR.inter hEq.compl).exists_of_finite).compl using 1
  ext a
  change (∀ z,Sum.elim a z ∈ R → iRv (z (.inr 0))=iRv (z (.inl (.inl j)))) ↔
    ¬ ∃ z : FocusEntryIndex n r → M,Sum.elim a z ∈ R ∧
      iRv (z (.inr 0)) ≠ iRv (z (.inl (.inl j)))
  simp only [not_exists,not_and,not_not]

theorem mem_focusLeadingTermParameterLocus_map_iff
    (R : Set (ι ⊕ FocusEntryIndex n r → M)) (a : ι → M) (j : Fin n)
    {A : DefSet (rawMixedSpace (M := M) n r) T}
    (f : Map A (DefSet.univ (rawVFSpace (M := M) 1) T))
    (hSection : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawVFSpace 1) f.graph) :
    a ∈ focusLeadingTermParameterLocus R j ↔
      ∀ p : A,rv M ((f p).val 0)=rv M (p.val.1 j) := by
  have hAt (z) : Sum.elim a z ∈ R ↔
      ∃ p : A,Sum.elim (mixedValues p.val) (vfValues (f p).val)=z :=
    (Set.ext_iff.mp hSection z).trans (scalarMapGraph_iff f z)
  constructor
  · intro h p
    exact Subtype.ext (h _ ((hAt _).mpr ⟨p,rfl⟩))
  · intro h z hz
    obtain ⟨p,rfl⟩ := (hAt z).mp hz
    exact congrArg Subtype.val (h p)

end DiamondIntegral.Section6
