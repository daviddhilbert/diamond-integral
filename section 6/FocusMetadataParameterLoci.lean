import «section 6».VFScalarNameTemplates
import «section 6».PromotedGammaNameTemplates
import «section 6».FocusCovarianceParameterLoci

/-! Finite named focus metadata enter geometric admissibility through
first-order quantification of their complete VF and Gamma name graphs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p : ℕ}

def focusMetadataParameterLocus (C : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (B : GammaNameParameterTemplate (M := M) S p) (L : Set (FocusMetadataIndex (Fin p) → M)) : Set (Fin p → M) :=
  {a | ∀ c b : Fin 1 → M,Sum.elim a (Sum.elim Fin.elim0 c) ∈ C.graph →
    Sum.elim a b ∈ B.graph → Sum.elim (Sum.elim a c) b ∈ L}

theorem focusMetadataParameterLocus_definable (C : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (B : GammaNameParameterTemplate (M := M) S p) (L : Set (FocusMetadataIndex (Fin p) → M))
    (hL : S.Definable LRV L) : S.Definable LRV (focusMetadataParameterLocus C B L) := by
  let Z := FocusMetadataIndex (Fin p)
  have hCCode : S.DefinableMap LRV (fun z : Z → M => Sum.elim (fun i => z (.inl (.inl i)))
      (Sum.elim (Fin.elim0 : Fin 0 → M) (fun i => z (.inl (.inr i))))) := by
    rintro (i | (i | i))
    · exact Set.DefinableFun.proj LRV
    · exact i.elim0
    · exact Set.DefinableFun.proj LRV
  have hBCode : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (fun i => z (.inl (.inl i))) (z ∘ Sum.inr)) := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hBad := ((C.definable.preimage_map hCCode).inter (B.definable.preimage_map hBCode)).inter hL.compl
  convert hBad.exists_of_finite.exists_of_finite.compl using 1
  ext a
  change (∀ c b : Fin 1 → M,Sum.elim a (Sum.elim Fin.elim0 c) ∈ C.graph →
    Sum.elim a b ∈ B.graph → Sum.elim (Sum.elim a c) b ∈ L) ↔
    ¬ ∃ c b : Fin 1 → M,(Sum.elim a (Sum.elim Fin.elim0 c) ∈ C.graph ∧ Sum.elim a b ∈ B.graph) ∧
      Sum.elim (Sum.elim a c) b ∉ L
  simp only [not_exists,not_and,not_not]
  exact ⟨fun h c b hc => h c b hc.1 hc.2,fun h c b hc hb => h c b ⟨hc,hb⟩⟩

def gammaTemplateRepresentative (B : GammaNameParameterTemplate (M := M) S p)
    (a : Fin p → M) (ha : a ∈ B.good) : RVInfinity M :=
  ⟨ha.1.choose 0,(B.proper _ ha.1.choose_spec).1⟩

theorem gammaTemplateRepresentative_nonzero (B : GammaNameParameterTemplate (M := M) S p)
    (a : Fin p → M) (ha : a ∈ B.good) : gammaTemplateRepresentative B a ha ≠ rvZero M := by
  intro h
  exact (B.proper _ ha.1.choose_spec).2 (congrArg Subtype.val h)

theorem focusMetadataParameterLocus_at (C : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (B : GammaNameParameterTemplate (M := M) S p) (L : Set (FocusMetadataIndex (Fin p) → M))
    (a : Fin p → M) (haC : a ∈ C.good) (haB : a ∈ B.good)
    (ha : a ∈ focusMetadataParameterLocus C B L) :
    Sum.elim (Sum.elim a (fun _ : Fin 1 => (vfScalarTemplateValue C a haC).val))
      (fun _ : Fin 1 => (gammaTemplateRepresentative B a haB).val) ∈ L := by
  have hScalar : vfValues (C.value a haC Fin.elim0)=
      (fun _ : Fin 1 => (vfScalarTemplateValue C a haC).val) := by funext i; fin_cases i; rfl
  have hEntry := C.value_mem a haC Fin.elim0
  have hEmpty : vfValues (Fin.elim0 : Fin 0 → VF M)=(Fin.elim0 : Fin 0 → M) := funext (fun i => i.elim0)
  rw [hEmpty,hScalar] at hEntry
  have hBeta : (fun _ : Fin 1 => (gammaTemplateRepresentative B a haB).val)=haB.1.choose := by
    funext i; fin_cases i; rfl
  exact ha _ _ hEntry (hBeta.symm ▸ haB.1.choose_spec)

end DiamondIntegral.Section6
