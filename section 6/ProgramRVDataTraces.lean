import «section 6».CentripetalProgramGeometry
import «section 6».ComponentMetadataRVTemplates

/-! The complete finite RV-data trace of a permitted program includes
every current ambient and protected image, actual active locus,
coefficient and Gamma name. Admissible fibres have bounded individual
rows; no uniform bound over the VF parameter family is inferred. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def unitRVDataTemplate (S : Set M) (p : ℕ) : RVSetParameterTemplate (M := M) S p 1 :=
  ⟨{z | z (.inr 0)=(branchTag (M := M) false).val},
    (show S.DefinableFun LRV (fun z : Fin p ⊕ Fin 1 → M => z (.inr 0)) from Set.DefinableFun.proj LRV).ofPred_eq
      (branchTag_definable S false)⟩

theorem unitRVDataTemplate_fibre (a : Fin p → M) :
    ((unitRVDataTemplate S p).fibre a).carrier={fun _ : Fin 1 => branchTag (M := M) false} := by
  ext u
  constructor
  · intro h
    apply Set.mem_singleton_iff.mpr
    funext i
    fin_cases i
    exact Subtype.ext h
  · intro h
    rw [Set.mem_singleton_iff.mp h]
    rfl

theorem unitRVDataTemplate_doublyBounded (a : Fin p → M) :
    RVValueDoublyBounded ((unitRVDataTemplate (M := M) S p).fibre a).carrier := by
  rw [unitRVDataTemplate_fibre]
  exact nonzero_scalar_rv_singleton_doublyBounded _ (branchTag_nonzero false)

theorem leadingRVImageTemplate_doublyBounded
    (A : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (hAD : VFDoublyBounded (A.fibre a).carrier) (hRV : RVSupportDoublyBounded (A.fibre a).carrier) :
    RVValueDoublyBounded ((leadingRVImageTemplate A).fibre a).carrier := by
  rw [leadingRVImageTemplate_fibre]
  exact mixedLeadingRV_image_doublyBounded _ hAD hRV

abbrev RVDataTemplate (S : Set M) (p : ℕ) := Σ m,RVSetParameterTemplate (M := M) S p m

def RVTraceRowsBounded (a : Fin p → M) (D : List (RVDataTemplate (M := M) S p)) : Prop :=
  ∀ T ∈ D,RVValueDoublyBounded (T.2.fibre a).carrier

theorem rvTraceRowsBounded_append (a : Fin p → M) {D E : List (RVDataTemplate (M := M) S p)}
    (hD : RVTraceRowsBounded a D) (hE : RVTraceRowsBounded a E) : RVTraceRowsBounded a (D++E) := by
  intro T hT
  rcases List.mem_append.mp hT with h | h
  · exact hD T h
  · exact hE T h

def sourceRVDataTrace (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) : List (RVDataTemplate (M := M) S p) :=
  ⟨1,unitRVDataTemplate S p⟩ :: ⟨n+r,leadingRVImageTemplate A⟩ ::
    List.ofFn (fun i => (⟨n+r,leadingRVImageTemplate (P i)⟩ : RVDataTemplate S p))

theorem sourceRVDataTrace_bounded
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (h : TemplateFibreGeometry A P a) : RVTraceRowsBounded a (sourceRVDataTrace A P) := by
  intro D hD
  simp only [sourceRVDataTrace,List.mem_cons,List.mem_ofFn] at hD
  rcases hD with rfl | rfl | ⟨i,rfl⟩
  · exact unitRVDataTemplate_doublyBounded a
  · exact leadingRVImageTemplate_doublyBounded A a h.doublyBounded h.proper.rvBounded
  · exact leadingRVImageTemplate_doublyBounded (P i) a (h.doublyBounded.mono (h.subset i)) (h.piecesProper i).rvBounded

def CentripetalProgramTemplate.boundaryRVTrace (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) : List (RVDataTemplate (M := M) S p) :=
  sourceRVDataTrace A P ++ sourceRVDataTrace (T.target A) (fun i => T.pieceTarget A (P i))

def CentripetalProgramTemplate.rvTrace : {r s : ℕ} → CentripetalProgramTemplate (M := M) S p n r s →
    (A : MixedSetParameterTemplate (M := M) S p n r) →
    (Fin k → MixedSetParameterTemplate (M := M) S p n r) → List (RVDataTemplate (M := M) S p)
  | _,_,.identity r,A,P => (CentripetalProgramTemplate.identity r).boundaryRVTrace A P
  | _,_,.regularize r,A,P => (CentripetalProgramTemplate.regularize r).boundaryRVTrace A P
  | r,_,.centripetal T,A,P => (CentripetalProgramTemplate.centripetal T).boundaryRVTrace A P ++
      [⟨n+r,leadingRVImageTemplate (focusActiveParameterTemplate A T.active)⟩,
        ⟨1,coefficientRVDataTemplate T.coefficient⟩,⟨1,gammaRVDataTemplate T.radius⟩]
  | _,_,.comp F H,A,P => F.rvTrace A P ++ H.rvTrace (F.target A) (fun i => F.pieceTarget A (P i))

theorem CentripetalProgramTemplate.boundaryRVTrace_bounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (ha : a ∈ T.good A P) (h : TemplateFibreGeometry A P a) : RVTraceRowsBounded a (T.boundaryRVTrace A P) := by
  obtain ⟨F⟩ := T.exists_realization h00 hc hκ hs hv A P a ha h.proper h.doublyBounded h.subset h.piecesProper
  exact rvTraceRowsBounded_append a (sourceRVDataTrace_bounded A P a h)
    (sourceRVDataTrace_bounded _ _ a (F.outputGeometry h00 hc hκ hs hv h))

theorem CentripetalProgramTemplate.rvTrace_bounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (ha : a ∈ T.good A P) (h : TemplateFibreGeometry A P a) : RVTraceRowsBounded a (T.rvTrace A P) := by
  induction T with
  | identity r => exact (CentripetalProgramTemplate.identity r).boundaryRVTrace_bounded h00 hc hκ hs hv A P a ha h
  | regularize r => exact (CentripetalProgramTemplate.regularize r).boundaryRVTrace_bounded h00 hc hκ hs hv A P a ha h
  | centripetal T =>
    apply rvTraceRowsBounded_append a ((CentripetalProgramTemplate.centripetal T).boundaryRVTrace_bounded h00 hc hκ hs hv A P a ha h)
    obtain ⟨D,hj,hU,hCoeff,hFocus,hE⟩ := T.exists_component hc hv A P a ha h.proper h.doublyBounded h.subset h.piecesProper
    have hc0 : vfScalarTemplateValue T.coefficient a ha.1.1.2 ≠ 0 := by
      rw [← hCoeff]
      exact D.coefficient_nonzero
    intro E hE
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hE
    rcases hE with rfl | rfl | rfl
    · apply leadingRVImageTemplate_doublyBounded
      · rw [focusActiveParameterTemplate_fibre]
        exact h.doublyBounded.mono (fun _ hx => hx.1)
      · rw [focusActiveParameterTemplate_fibre]
        exact h.proper.rvBounded.mono (fun _ hx => hx.1)
    · exact coefficientRVDataTemplate_doublyBounded T.coefficient a ha.1.1.2 hc0
    · exact gammaRVDataTemplate_doublyBounded T.radius a ha.1.2
  | comp F H ihF ihH =>
    obtain ⟨f⟩ := F.exists_realization h00 hc hκ hs hv A P a ha.1 h.proper h.doublyBounded h.subset h.piecesProper
    exact rvTraceRowsBounded_append a (ihF A P ha.1 h)
      (ihH (F.target A) (fun i => F.pieceTarget A (P i)) ha.2 (f.outputGeometry h00 hc hκ hs hv h))

end DiamondIntegral.Section6
