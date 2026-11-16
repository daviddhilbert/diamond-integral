import «section 6».RVIndexedRowBounds
import Section8.ContinuityFamilies

/-! Total scalar VF function families with RV parameters. Their full
raw graphs and continuity loci are defined over the original base;
fixing the existing RV labels gives the actual VF graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def rvFunctionFamilyInputs : Set (Fin r ⊕ Fin n → M) :=
  {z | (∀ i, iRV (z (.inl i))) ∧ ∀ i, iVF (z (.inr i))}

theorem rvFunctionFamilyInputs_definable (S : Set M) :
    S.Definable LRV (rvFunctionFamilyInputs (M := M) (n := n) (r := r)) := by
  have hRV (i : Fin r) : S.Definable LRV {z : Fin r ⊕ Fin n → M | iRV (z (.inl i))} :=
    (definableAt_sort S .rv).raw_definable.preimage_comp (fun _ : Fin 1 => (Sum.inl i : Fin r ⊕ Fin n))
  have hVF (i : Fin n) : S.Definable LRV {z : Fin r ⊕ Fin n → M | iVF (z (.inr i))} :=
    (definableAt_sort S .vf).raw_definable.preimage_comp (fun _ : Fin 1 => (Sum.inr i : Fin r ⊕ Fin n))
  convert (Set.definable_iInter_of_finite hRV).inter (Set.definable_iInter_of_finite hVF) using 1
  ext z
  simp only [rvFunctionFamilyInputs,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]

def rvFunctionFamilyArgs (z : Fin r ⊕ (Fin n ⊕ Fin 1) → M) : Fin r ⊕ Fin n → M :=
  Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (.inl i)))

def rvFunctionFamilyGraph (F : (Fin r ⊕ Fin n → M) → M) :
    Set (Fin r ⊕ (Fin n ⊕ Fin 1) → M) :=
  {z | rvFunctionFamilyArgs z ∈ rvFunctionFamilyInputs ∧ F (rvFunctionFamilyArgs z) = z (.inr (.inr 0))}

theorem rvFunctionFamilyGraph_definable (F : (Fin r ⊕ Fin n → M) → M)
    (hF : S.DefinableFun LRV F) : S.Definable LRV (rvFunctionFamilyGraph F) := by
  have hArgs : S.DefinableMap LRV (rvFunctionFamilyArgs (M := M) (n := n) (r := r)) := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  exact ((rvFunctionFamilyInputs_definable S).preimage_map hArgs).inter
    ((hF.comp hArgs).ofPred_eq (Set.DefinableFun.proj LRV))

theorem rvFunctionFamilyGraph_section
    (F : (Fin r ⊕ Fin n → M) → M)
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin 1 → VF M)
    (hAt : ∀ u a, F (Sum.elim (rvValues u) (vfValues a)) = (f u a 0).val)
    (u : Fin r → RVInfinity M) :
    {w : Fin n ⊕ Fin 1 → M | Sum.elim (rvValues u) w ∈ rvFunctionFamilyGraph F} = vfGraph (f u) := by
  ext w
  constructor
  · rintro ⟨⟨hRV,hVF⟩,hval⟩
    let a : Fin n → VF M := fun i => ⟨w (.inl i),hVF i⟩
    have hArgs : rvFunctionFamilyArgs (Sum.elim (rvValues u) w) = Sum.elim (rvValues u) (vfValues a) := rfl
    have hOut : (f u a 0).val = w (.inr 0) := (hAt u a).symm.trans hval
    refine ⟨a,?_⟩
    funext i
    cases i with
    | inl i => rfl
    | inr i => fin_cases i; exact hOut
  · rintro ⟨a,ha⟩
    have hInput (i : Fin n) : (a i).val = w (.inl i) := congrFun ha (.inl i)
    have hArgs : rvFunctionFamilyArgs (Sum.elim (rvValues u) w) = Sum.elim (rvValues u) (vfValues a) := by
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact (hInput i).symm
    refine ⟨⟨fun i => (u i).property,fun i => ?_⟩,?_⟩
    · change iVF (w (.inl i))
      rw [← hInput i]
      exact (a i).property
    · change F (rvFunctionFamilyArgs (Sum.elim (rvValues u) w)) = w (.inr 0)
      rw [hArgs,hAt]
      exact congrFun ha (.inr 0)

def rvFunctionFamilyBadInputs (F : (Fin r ⊕ Fin n → M) → M) : Set (Fin r ⊕ Fin n → M) :=
  rvFunctionFamilyInputs \ continuousInputsFamily (rvFunctionFamilyGraph F)

theorem rvFunctionFamilyBadInputs_definable (F : (Fin r ⊕ Fin n → M) → M)
    (hF : S.DefinableFun LRV F) : S.Definable LRV (rvFunctionFamilyBadInputs F) :=
  (rvFunctionFamilyInputs_definable S).sdiff
    (continuousInputsFamily_definable (rvFunctionFamilyGraph_definable F hF))

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem rvFunctionFamilyBadInputs_at
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : (Fin r ⊕ Fin n → M) → M)
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin 1 → VF M)
    (hAt : ∀ u a, F (Sum.elim (rvValues u) (vfValues a)) = (f u a 0).val)
    (u : Fin r → RVInfinity M) (a : Fin n → VF M) :
    Sum.elim (rvValues u) (vfValues a) ∈ rvFunctionFamilyBadInputs F ↔ ¬ ContinuousAt (f u) a := by
  change ((∀ i, iRV (u i).val) ∧ (∀ i, iVF (a i).val)) ∧
    vfValues a ∉ continuousInputs {w | Sum.elim (rvValues u) w ∈ rvFunctionFamilyGraph F} ↔ _
  rw [rvFunctionFamilyGraph_section F f hAt u,mem_continuousInputs_iff hv]
  exact and_iff_right ⟨fun i => (u i).property,fun i => (a i).property⟩

end DiamondIntegral.Section6
