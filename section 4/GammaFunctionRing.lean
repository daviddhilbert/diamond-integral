import «section 4».GammaDefinableConvolution

/-! The raw carrier of all finite-range original-base definable unary
functions, with its Euler convolution ring transported along the proved
bijection. Evaluation theorems identify the operations on actual functions. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section4.GammaFunctionRing
open GammaDefinableEuler GammaDefinableFunctions GammaDefinableConvolution EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def DefinableFunction (B : GammaParameters.Base (M := M)) :=
  {f : PaperGamma (M := M) → ℤ // IntegerDefinable B (fun γ => f (toPaperGamma γ))}

def evaluate (B : GammaParameters.Base (M := M)) (k : EulerKind) :
    baseSubring B k → DefinableFunction B := fun f => ⟨f.val, f.property⟩

theorem evaluate_injective (B : GammaParameters.Base (M := M)) (k : EulerKind) :
    Function.Injective (evaluate B k) := by
  intro f g h
  apply Subtype.ext
  apply eval_injective k
  exact congrArg (fun p : DefinableFunction B => p.val) h

theorem evaluate_surjective (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (k : EulerKind) : Function.Surjective (evaluate B k) := by
  intro f
  obtain ⟨g, hg⟩ := exists_eulerFunction_of_definable h00 B k f.val f.property.1 f.property.2
  have he : (fun γ : Values.Gamma (M := M) => g (toPaperGamma γ)) =
      (fun γ => f.val (toPaperGamma γ)) := funext (fun γ => hg (toPaperGamma γ))
  have hgb : g ∈ baseSubring B k := by
    change IntegerDefinable B (fun γ => g (toPaperGamma γ))
    rw [he]
    exact f.property
  exact ⟨⟨g, hgb⟩, Subtype.ext (funext hg)⟩

def evaluationEquiv (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (k : EulerKind) : baseSubring B k ≃ DefinableFunction B :=
  Equiv.ofBijective (evaluate B k) ⟨evaluate_injective B k, evaluate_surjective h00 B k⟩

@[instance_reducible]
def functionCommRing (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (k : EulerKind) : CommRing (DefinableFunction B) :=
  (evaluationEquiv h00 B k).symm.commRing

def toEulerRingEquiv (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (k : EulerKind) : by
    letI := functionCommRing h00 B k
    exact DefinableFunction B ≃+* baseSubring B k :=
  Equiv.ringEquiv (evaluationEquiv h00 B k).symm

theorem toEuler_eval (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (k : EulerKind) (f : DefinableFunction B)
    (t : PaperGamma (M := M)) : ((toEulerRingEquiv h00 B k f).val) t = f.val t := by
  have h := congrArg Subtype.val ((evaluationEquiv h00 B k).apply_symm_apply f)
  exact congrFun h t

theorem add_eval (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (k : EulerKind)
    (f g : DefinableFunction B) (t : PaperGamma (M := M)) : by
    letI := functionCommRing h00 B k
    exact (f + g).val t = f.val t + g.val t := by
  let := functionCommRing h00 B k
  have h := (toEulerRingEquiv h00 B k).map_add f g
  calc
    (f + g).val t = ((toEulerRingEquiv h00 B k (f + g)).val) t :=
      (toEuler_eval h00 B k (f + g) t).symm
    _ = ((toEulerRingEquiv h00 B k f + toEulerRingEquiv h00 B k g).val) t := by rw [h]
    _ = f.val t + g.val t := by rw [Subring.coe_add, eval_add, toEuler_eval, toEuler_eval]

theorem mul_eval (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (k : EulerKind)
    (f g : DefinableFunction B) (t : PaperGamma (M := M)) : by
    letI := functionCommRing h00 B k
    exact (f * g).val t = convolutionValue k (toEulerRingEquiv h00 B k f).val
      (toEulerRingEquiv h00 B k g).val t := by
  let := functionCommRing h00 B k
  rw [convolutionValue_eq_product, ← Subring.coe_mul, ← (toEulerRingEquiv h00 B k).map_mul]
  exact (toEuler_eval h00 B k (f * g) t).symm

theorem one_eval (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (k : EulerKind) (t : PaperGamma (M := M)) : by
    letI := functionCommRing h00 B k
    exact (1 : DefinableFunction B).val t = if t = 0 then 1 else 0 := by
  let := functionCommRing h00 B k
  rw [← toEuler_eval h00 B k 1 t, map_one]
  change (1 : EulerFunction k (PaperGamma (M := M))) t = _
  rw [← point_zero k, point_eval]

end DiamondIntegral.Section4.GammaFunctionRing
