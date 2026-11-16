import «section 2».Differentiation

/-! R102: total derivatives compose on the complement of the pulled-back
exceptional loci. No chain rule for merely partial derivatives is used.
These are the fixed-RV-chart analytic statements; the global dimension
and definability assembly is tracked separately. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m l : ℕ}

theorem derivative_comp
    {f : (Fin n → VF M) → Fin m → VF M}
    {g : (Fin m → VF M) → Fin l → VF M} {a : Fin n → VF M}
    {L : (Fin n → VF M) →ₗ[VF M] (Fin m → VF M)}
    {D : (Fin m → VF M) →ₗ[VF M] (Fin l → VF M)}
    (hf : HasDerivativeAt f a L) (hg : HasDerivativeAt g (f a) D) :
    HasDerivativeAt (g ∘ f) a (D.comp L) :=
  (hasDerivativeAt_iff_companion _ _ _).mpr
    (((hasDerivativeAt_iff_companion _ _ _).mp hg).comp
      ((hasDerivativeAt_iff_companion _ _ _).mp hf))

def HasUnitJacobianAt (f : (Fin n → VF M) → Fin n → VF M)
    (a : Fin n → VF M) : Prop :=
  ∃ L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M),
    HasDerivativeAt f a L ∧ (LinearMap.toMatrix' L).det = 1

theorem HasUnitJacobianAt.partialJacobian
    {f : (Fin n → VF M) → Fin n → VF M} {a : Fin n → VF M}
    (hf : HasUnitJacobianAt f a) : HasVFJacobianAt f a 1 := by
  obtain ⟨L,hL,hdet⟩ := hf
  rw [← hdet]
  exact ((hasDerivativeAt_iff_companion _ _ _).mp hL).hasJacobianAt

theorem HasUnitJacobianAt.comp
    {f g : (Fin n → VF M) → Fin n → VF M} {a : Fin n → VF M}
    (hg : HasUnitJacobianAt g (f a)) (hf : HasUnitJacobianAt f a) :
    HasUnitJacobianAt (g ∘ f) a := by
  obtain ⟨L,hL,hLd⟩ := hf
  obtain ⟨D,hD,hDd⟩ := hg
  refine ⟨D.comp L,derivative_comp hL hD,?_⟩
  rw [LinearMap.toMatrix'_comp,Matrix.det_mul,hDd,hLd,mul_one]

theorem hasUnitJacobianAt_id (a : Fin n → VF M) : HasUnitJacobianAt id a := by
  refine ⟨LinearMap.id,?_,?_⟩
  · apply (hasDerivativeAt_iff_companion _ _ _).mpr
    convert hasVFDerivativeAt_affine
      (LinearMap.id : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M)) 0 a using 1
    funext x
    simp only [LinearMap.id_apply,add_zero,id_eq]
  · simp only [LinearMap.toMatrix'_id,Matrix.det_one]

theorem hasUnitJacobianAt_zero_arity
    (f : (Fin 0 → VF M) → Fin 0 → VF M) (a : Fin 0 → VF M) :
    HasUnitJacobianAt f a := by
  have he : f = id := funext (fun _ => Subsingleton.elim _ _)
  rw [he]
  exact hasUnitJacobianAt_id a

def UnitJacobianOff (A E : Set (Fin n → VF M))
    (f : (Fin n → VF M) → Fin n → VF M) : Prop :=
  ∀ a ∈ A \ E, HasUnitJacobianAt f a

/-- The bad locus includes failures at the first stage and failures
at the image point of the second stage. -/
theorem UnitJacobianOff.comp
    {A B E F : Set (Fin n → VF M)}
    {f g : (Fin n → VF M) → Fin n → VF M}
    (hf : UnitJacobianOff A E f) (hg : UnitJacobianOff B F g)
    (hmap : Set.MapsTo f A B) :
    UnitJacobianOff A (E ∪ f ⁻¹' F) (g ∘ f) := by
  rintro a ⟨ha,hbad⟩
  apply HasUnitJacobianAt.comp
  · exact hg (f a) ⟨hmap ha,fun h => hbad (Or.inr h)⟩
  · exact hf a ⟨ha,fun h => hbad (Or.inl h)⟩

theorem hasUnitJacobianAt_translation (b a : Fin n → VF M) :
    HasUnitJacobianAt (fun x => x + b) a := by
  refine ⟨LinearMap.id,?_,?_⟩
  · apply (hasDerivativeAt_iff_companion _ _ _).mpr
    exact hasVFDerivativeAt_affine LinearMap.id b a
  · simp only [LinearMap.toMatrix'_id,Matrix.det_one]

abbrev JacobianStage (M : Type) [LRV.Structure M] (n : ℕ) :=
  (((Fin n → VF M) → Fin n → VF M) × Set (Fin n → VF M))

def stageComposite : List (JacobianStage M n) → (Fin n → VF M) → Fin n → VF M
  | [] => id
  | stage :: rest => stageComposite rest ∘ stage.1

def stageExceptions : List (JacobianStage M n) → Set (Fin n → VF M)
  | [] => ∅
  | stage :: rest => stage.2 ∪ stage.1 ⁻¹' stageExceptions rest

theorem stageComposite_unit_off (stages : List (JacobianStage M n))
    (hstage : ∀ stage ∈ stages, UnitJacobianOff Set.univ stage.2 stage.1) :
    UnitJacobianOff Set.univ (stageExceptions stages) (stageComposite stages) := by
  induction stages with
  | nil => exact fun a _ => hasUnitJacobianAt_id a
  | cons stage rest ih =>
    exact (hstage stage (by simp)).comp
      (ih (fun s hs => hstage s (by simp only [List.mem_cons]; exact Or.inr hs)))
      (fun _ _ => Set.mem_univ _)

/-- The matrix in R102 cannot support the old everywhere conclusion. -/
theorem r102_partial_matrix_det_zero (K : Type*) [CommRing K] :
    Matrix.det (!![1,1,0; 1,1,0; 1,0,1] : Matrix (Fin 3) (Fin 3) K) = 0 := by
  simp [Matrix.det_fin_three]

end DiamondIntegral.Section6
