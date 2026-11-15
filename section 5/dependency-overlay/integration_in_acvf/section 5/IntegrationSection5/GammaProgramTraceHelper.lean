import IntegrationSection5.GammaTraceCore

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
open SpecialTransformations.Section3
variable {G : GammaParameters.Base (M := M)} {S : Set M}
theorem gamma_uniform_trace_append {n a b c : ℕ} {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    {C : DefSet (M := M) S n c} (T : UniformRelativeTrace S n A B) (U : UniformRelativeTrace S n B C)
    (hT : GammaUniformTrace (G := G) T) (hU : GammaUniformTrace (G := G) U) :
    GammaUniformTrace (G := G) (T.append U) := by
  induction T with
  | nil A => exact hU
  | canonical i tail ih => exact ⟨hT.1,ih U hT.2 hU⟩
  | focus D tail ih => exact ⟨hT.1,hT.2.1,ih U hT.2.2 hU⟩

structure ProgramNaturalTrace {n m l : ℕ} {A : DefSet (M := M) S n m} {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S A U) where
  arity : ℕ
  target : DefSet (M := M) S n arity
  trace : UniformRelativeTrace S n A target
  projection : Fin l → Fin arity
  square : ∀ a : A, fullRVProjection projection (trace.toMap a).val = (T.naturalMap a).val


end IntegrationInACVF.Section5
