import «section 6».ProgramCompositionIdentities

/-! Finite programs admit a sequential presentation with exactly
the same full graphs, admissibility loci and complete RV data traces.
Identity steps are retained, so no domain clipping is suppressed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s t k : ℕ}

structure CentripetalProgramTemplate.SameData
    (F H : CentripetalProgramTemplate (M := M) S p n r s) : Prop where
  transition : ∀ A,F.transition A=H.transition A
  good : ∀ {k} A (P : Fin k → MixedSetParameterTemplate (M := M) S p n r),F.good A P=H.good A P
  rvTrace : ∀ {k} A (P : Fin k → MixedSetParameterTemplate (M := M) S p n r),F.rvTrace A P=H.rvTrace A P

namespace CentripetalProgramTemplate.SameData

theorem refl (F : CentripetalProgramTemplate (M := M) S p n r s) : F.SameData F :=
  ⟨fun _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩

theorem trans {F H K : CentripetalProgramTemplate (M := M) S p n r s}
    (hFH : F.SameData H) (hHK : H.SameData K) : F.SameData K :=
  ⟨fun A => (hFH.transition A).trans (hHK.transition A),
    fun A P => (hFH.good A P).trans (hHK.good A P),
    fun A P => (hFH.rvTrace A P).trans (hHK.rvTrace A P)⟩

theorem target {F H : CentripetalProgramTemplate (M := M) S p n r s}
    (h : F.SameData H) (A : MixedSetParameterTemplate (M := M) S p n r) : F.target A=H.target A :=
  congrArg (fun R : MixedTransitionParameterTemplate (M := M) S p n r s => R.image A) (h.transition A)

theorem pieceTarget {F H : CentripetalProgramTemplate (M := M) S p n r s}
    (h : F.SameData H) (A C : MixedSetParameterTemplate (M := M) S p n r) :
    F.pieceTarget A C=H.pieceTarget A C :=
  congrArg (fun R : MixedTransitionParameterTemplate (M := M) S p n r s => R.image C) (h.transition A)

theorem preparedGood {F H : CentripetalProgramTemplate (M := M) S p n r s}
    (h : F.SameData H) (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) : F.preparedGood A P=H.preparedGood A P := by
  simp only [CentripetalProgramTemplate.preparedGood,h.good,h.pieceTarget]

theorem comp {F F' : CentripetalProgramTemplate (M := M) S p n r s}
    {H H' : CentripetalProgramTemplate (M := M) S p n s t}
    (hF : F.SameData F') (hH : H.SameData H') : (F.comp H).SameData (F'.comp H') := by
  constructor
  · intro A
    change MixedTransitionParameterTemplate.mk _ _=MixedTransitionParameterTemplate.mk _ _
    congr 1
    change parameterRelationComp (F.transition A).graph (H.transition (F.target A)).graph=
      parameterRelationComp (F'.transition A).graph (H'.transition (F'.target A)).graph
    rw [hF.transition A,hF.target A,hH.transition]
  · intro k A P
    have hPieces : (fun i => F.pieceTarget A (P i))=(fun i => F'.pieceTarget A (P i)) :=
      funext (fun i => hF.pieceTarget A (P i))
    change F.good A P ∩ H.good (F.target A) (fun i => F.pieceTarget A (P i))=_
    rw [hF.good,hF.target,hPieces,hH.good]
    rfl
  · intro k A P
    have hPieces : (fun i => F.pieceTarget A (P i))=(fun i => F'.pieceTarget A (P i)) :=
      funext (fun i => hF.pieceTarget A (P i))
    change F.rvTrace A P ++ H.rvTrace (F.target A) (fun i => F.pieceTarget A (P i))=_
    rw [hF.rvTrace,hF.target,hPieces,hH.rvTrace]
    rfl

theorem assoc (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    {v : ℕ} (K : CentripetalProgramTemplate (M := M) S p n t v) :
    ((F.comp H).comp K).SameData (F.comp (H.comp K)) :=
  ⟨F.transition_comp_assoc H K,F.good_comp_assoc H K,F.rvTrace_comp_assoc H K⟩

end CentripetalProgramTemplate.SameData

inductive CentripetalProgramPrimitive (S : Set M) (p n : ℕ) : ℕ → ℕ → Type where
  | identity (r : ℕ) : CentripetalProgramPrimitive S p n r r
  | regularize (r : ℕ) : CentripetalProgramPrimitive S p n r (n+r)
  | centripetal {r : ℕ} (T : FocusComponentParameterTemplate (M := M) S p n r) :
      CentripetalProgramPrimitive S p n r (1+r)

def CentripetalProgramPrimitive.toProgram : {r s : ℕ} →
    CentripetalProgramPrimitive (M := M) S p n r s → CentripetalProgramTemplate (M := M) S p n r s
  | _,_,.identity r => .identity r
  | _,_,.regularize r => .regularize r
  | _,_,.centripetal T => .centripetal T

inductive CentripetalProgramSequence (S : Set M) (p n : ℕ) : ℕ → ℕ → Type where
  | single {r s : ℕ} (F : CentripetalProgramPrimitive (M := M) S p n r s) :
      CentripetalProgramSequence S p n r s
  | cons {r s t : ℕ} (F : CentripetalProgramPrimitive (M := M) S p n r s)
      (H : CentripetalProgramSequence S p n s t) : CentripetalProgramSequence S p n r t

namespace CentripetalProgramSequence

def toProgram : {r s : ℕ} → CentripetalProgramSequence (M := M) S p n r s →
    CentripetalProgramTemplate (M := M) S p n r s
  | _,_,.single F => F.toProgram
  | _,_,.cons F H => F.toProgram.comp H.toProgram

def append : {r s t : ℕ} → CentripetalProgramSequence (M := M) S p n r s →
    CentripetalProgramSequence (M := M) S p n s t → CentripetalProgramSequence (M := M) S p n r t
  | _,_,_,.single F,H => .cons F H
  | _,_,_,.cons F K,H => .cons F (K.append H)

def steps : {r s : ℕ} → CentripetalProgramSequence (M := M) S p n r s → ℕ
  | _,_,.single _ => 1
  | _,_,.cons _ H => H.steps+1

theorem steps_pos (F : CentripetalProgramSequence (M := M) S p n r s) : 0<F.steps := by
  cases F <;> simp only [steps] <;> omega

theorem append_steps (F : CentripetalProgramSequence (M := M) S p n r s)
    (H : CentripetalProgramSequence (M := M) S p n s t) : (F.append H).steps=F.steps+H.steps := by
  induction F with
  | single F => simp only [append,steps]; omega
  | cons F K ih => simp only [append,steps,ih]; omega

theorem append_sameData (F : CentripetalProgramSequence (M := M) S p n r s)
    (H : CentripetalProgramSequence (M := M) S p n s t) :
    (F.toProgram.comp H.toProgram).SameData (F.append H).toProgram := by
  induction F with
  | single F => exact CentripetalProgramTemplate.SameData.refl _
  | cons F K ih =>
    exact (CentripetalProgramTemplate.SameData.assoc F.toProgram K.toProgram H.toProgram).trans
      ((CentripetalProgramTemplate.SameData.refl F.toProgram).comp (ih H))

end CentripetalProgramSequence

def CentripetalProgramTemplate.toSequence : {r s : ℕ} → CentripetalProgramTemplate (M := M) S p n r s →
    CentripetalProgramSequence (M := M) S p n r s
  | _,_,.identity r => .single (.identity r)
  | _,_,.regularize r => .single (.regularize r)
  | _,_,.centripetal T => .single (.centripetal T)
  | _,_,.comp F H => F.toSequence.append H.toSequence

theorem CentripetalProgramTemplate.toSequence_sameData
    (F : CentripetalProgramTemplate (M := M) S p n r s) : F.SameData F.toSequence.toProgram := by
  induction F with
  | identity r => exact CentripetalProgramTemplate.SameData.refl _
  | regularize r => exact CentripetalProgramTemplate.SameData.refl _
  | centripetal T => exact CentripetalProgramTemplate.SameData.refl _
  | comp F H ihF ihH => exact (ihF.comp ihH).trans (F.toSequence.append_sameData H.toSequence)

end DiamondIntegral.Section6
