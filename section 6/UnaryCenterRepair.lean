import «section 6».UnaryExceptionalRVLabels

/-! Replace a unary center function on whole exceptional input RV
discs. Local constancy of the nonzero input leading term preserves the
good derivatives and makes each replacement branch constant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def repairedUnaryCenters (B : Set M) (f : (Fin 2 → M) → VF M)
    (g : (Fin 1 → M) → VF M) (z : Fin 2 → M) : VF M :=
  if iRv (z 0) ∈ B then g (fun _ => z 1) else f z

theorem repairedUnaryCenters_definable (B : Set M) (hB : S.Definable₁ LRV B)
    (f : (Fin 2 → M) → VF M) (hf : S.DefinableFun LRV (fun z => (f z).val))
    (g : (Fin 1 → M) → VF M) (hg : S.DefinableFun LRV (fun z => (g z).val)) :
    S.DefinableFun LRV (fun z => (repairedUnaryCenters B f g z).val) := by
  have hrv : S.DefinableMap LRV (fun z : Fin 2 → M => fun _ : Fin 1 => iRv (z 0)) :=
    fun _ => rv_scalarCode_definable (Set.DefinableFun.proj LRV)
  have hpred := hB.preimage_map hrv
  change S.Definable LRV {z : Fin 2 → M | iRv (z 0) ∈ B} at hpred
  have hG := hg.comp (show S.DefinableMap LRV (fun z : Fin 2 → M => fun _ : Fin 1 => z 1) from
    fun _ => Set.DefinableFun.proj LRV)
  simpa only [repairedUnaryCenters,apply_ite] using Set.DefinableFun.ite hpred hG hf

theorem repairedUnaryCenters_at (B : Set M) (f : (Fin 2 → M) → VF M)
    (g : (Fin 1 → M) → VF M) (a : Fin 1 → VF M) (v : M) :
    repairedUnaryCenters B f g (Fin.snoc (vfValues a) v) =
      if iRv (a 0).val ∈ B then g (fun _ => v) else f (Fin.snoc (vfValues a) v) := rfl

theorem unary_rv_ball (a : Fin 1 → VF M) (ha : a 0 ≠ 0) :
    ∃ δ : Gamma M, ∀ x ∈ vfBall a δ, rv M (x 0) = rv M (a 0) := by
  let δ : Gamma M := ⟨vfValue (a 0),fun he => ha ((vfValue_eq_infinity_iff _).mp he)⟩
  refine ⟨δ,fun x hx => rv_eq_of_close_at_radius δ le_rfl (hx 0)⟩

theorem repairedUnaryCenterMap_agrees (B : Set M) (hB : S.Definable₁ LRV B)
    (f : (Fin 2 → M) → VF M) (hf : S.DefinableFun LRV (fun z => (f z).val))
    (g : (Fin 1 → M) → VF M) (hg : S.DefinableFun LRV (fun z => (g z).val))
    (A : DefSet (rawMixedSpace (M := M) 1 1) S) (p : A)
    (hp : iRv (p.val.1 0).val ∉ B) :
    (unaryCenterMap (repairedUnaryCenters B f g) (repairedUnaryCenters_definable B hB f hf g hg) A p).val =
      (unaryCenterMap f hf A p).val := by
  change unaryCenterPoint (repairedUnaryCenters B f g) p.val = unaryCenterPoint f p.val
  simp only [unaryCenterPoint,repairedUnaryCenters_at,hp,ite_false]

theorem repairedUnaryCenterMap_good_derivative (B : Set M) (hB : S.Definable₁ LRV B)
    (f : (Fin 2 → M) → VF M) (hf : S.DefinableFun LRV (fun z => (f z).val))
    (g : (Fin 1 → M) → VF M) (hg : S.DefinableFun LRV (fun z => (g z).val))
    (A : DefSet (rawMixedSpace (M := M) 1 1) S) (p : A)
    (hp0 : p.val.1 0 ≠ 0) (hpB : iRv (p.val.1 0).val ∉ B)
    (L : (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M))
    (hL : HasMixedVFDerivativeAt (unaryCenterMap f hf A) p L) :
    HasMixedVFDerivativeAt
      (unaryCenterMap (repairedUnaryCenters B f g) (repairedUnaryCenters_definable B hB f hf g hg) A) p L := by
  obtain ⟨F,⟨ρ,hρ⟩,hD⟩ := hL
  obtain ⟨δ,hδ⟩ := unary_rv_ball p.val.1 hp0
  refine ⟨F,⟨max ρ δ,fun x hx => ?_⟩,hD⟩
  obtain ⟨hxA,hfx⟩ := hρ x (vfBall_anti (le_max_left _ _) hx)
  have hrv : iRv (x 0).val = iRv (p.val.1 0).val :=
    congrArg Subtype.val (hδ x (vfBall_anti (le_max_right _ _) hx))
  have hxB : iRv (x 0).val ∉ B := by rw [hrv]; exact hpB
  exact ⟨hxA,(repairedUnaryCenterMap_agrees B hB f hf g hg A ⟨(x,p.val.2),hxA⟩ hxB).trans hfx⟩

theorem repairedUnaryCenterMap_bad_derivative (B : Set M) (hB : S.Definable₁ LRV B)
    (f : (Fin 2 → M) → VF M) (hf : S.DefinableFun LRV (fun z => (f z).val))
    (g : (Fin 1 → M) → VF M) (hg : S.DefinableFun LRV (fun z => (g z).val))
    (R : M → M → Prop)
    (hR : S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M | R (z (.inl 0)) (z (.inr 0))})
    (p : unaryRVRelationDomain R hR) (hp0 : p.val.1 0 ≠ 0) (hpB : iRv (p.val.1 0).val ∈ B) :
    HasMixedVFDerivativeAt
      (unaryCenterMap (repairedUnaryCenters B f g) (repairedUnaryCenters_definable B hB f hf g hg)
        (unaryRVRelationDomain R hR)) p 0 := by
  obtain ⟨δ,hδ⟩ := unary_rv_ball p.val.1 hp0
  let c : Fin 1 → VF M := fun _ => g (fun _ => (p.val.2 0).val)
  have hD : HasVFDerivativeAt (fun _ : Fin 1 → VF M => c) p.val.1 0 := by
    simpa only [LinearMap.zero_apply,zero_add] using hasVFDerivativeAt_affine
      (0 : (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M)) c p.val.1
  refine ⟨(fun _ => c),⟨δ,fun x hx => ?_⟩,hD⟩
  have hrv : iRv (x 0).val = iRv (p.val.1 0).val := congrArg Subtype.val (hδ x hx)
  have hxA : (x,p.val.2) ∈ (unaryRVRelationDomain R hR).carrier := by
    change R (iRv (x 0).val) (p.val.2 0).val
    rw [hrv]
    exact p.property
  refine ⟨hxA,?_⟩
  change unaryCenterPoint (repairedUnaryCenters B f g) (x,p.val.2) = (c,p.val.2)
  simp only [unaryCenterPoint,repairedUnaryCenters_at,hrv,hpB,ite_true,c]

end DiamondIntegral.Section6
