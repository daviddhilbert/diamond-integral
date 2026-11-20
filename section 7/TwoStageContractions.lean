import «section 7».FirstStage
import «section 6».NormalizedMeasuredContractions
import «section 6».ZeroCenteredHomeomorphism

/-! Standard contractions of a `2`-dimensional object with prescribed stages
(for Lemma 7.21).

Given a zero-centred normalization `D` of `A ⊆ VF² × RVʳ`, a coordinate order
`e`, a first stage `S₁` on the prepared set, a second stage `S₂` on its
contracted set, and an RV form `ρ` on the final RV target through which the form
of `A` factors, `twoStage` is the normalized measured contraction of `(A, ω)`
in the order `e` with exactly these stages. Its first stage and rest are `S₁`
and the program `S₂`, so `FirstStage` computes its head-start class. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.TwoStageContractions
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.FirstStage

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {S : Set M} (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable {r : ℕ} {A : DefSet (rawMixedSpace (M := M) 2 r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} {e : Equiv.Perm (Fin 2)}

/-- The preparation map: normalization, then relabelling by `e`. -/
def prepOf (D : ZeroCenteredData A) (e : Equiv.Perm (Fin 2)) : Map A (reindexedVFSet D.map.image e) :=
  (vfRelabeling D.map.image e).comp D.bijection

include h00 in
theorem prepOf_bijective (D : ZeroCenteredData A) (e : Equiv.Perm (Fin 2)) : Function.Bijective (prepOf D e) :=
  (vfRelabeling_bijective _ e).comp (D.bijective h00)

/-- The form of `A` transported to the prepared set. -/
def preparedFormOf (D : ZeroCenteredData A) (e : Equiv.Perm (Fin 2)) :
    Map (reindexedVFSet D.map.image e) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  ω.comp ((prepOf D e).inverse (prepOf_bijective h00 D e))

theorem preparedFormOf_transport (D : ZeroCenteredData A) (e : Equiv.Perm (Fin 2)) (p : A) :
    (preparedFormOf (ω := ω) h00 D e (prepOf D e p)).val = (ω p).val := by
  change (ω ((prepOf D e).inverse (prepOf_bijective h00 D e) (prepOf D e p))).val = _
  rw [Map.inverse_apply]

variable {D : ZeroCenteredData A}

/-- The ordered program with stages `S₁`, `S₂`. -/
def twoStageProgram (S₁ : StandardContractionStage (G := G) (reindexedVFSet D.map.image e))
    (S₂ : StandardContractionStage (G := G) S₁.contracted) :
    OrderedStandardContractionProgram (G := G) S (reindexedVFSet D.map.image e) S₂.contracted :=
  .step S₁ (.step S₂ (.zero S₂.contracted))

theorem twoStageProgram_toMap (S₁ : StandardContractionStage (G := G) (reindexedVFSet D.map.image e))
    (S₂ : StandardContractionStage (G := G) S₁.contracted) (p : reindexedVFSet D.map.image e) :
    (twoStageProgram S₁ S₂).toMap p = S₂.contraction (S₁.contraction p) := rfl

/-- **The normalized measured contraction with prescribed stages.** -/
def twoStage (D : ZeroCenteredData A) (S₁ : StandardContractionStage (G := G) (reindexedVFSet D.map.image e))
    (S₂ : StandardContractionStage (G := G) S₁.contracted)
    (ρ : Map S₂.contracted (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hfactor : ∀ p : A, (ρ (S₂.contraction (S₁.contraction (prepOf D e p)))).val = (ω p).val) :
    NormalizedMeasuredContraction (G := G) A ω e where
  normalization := D
  preparedForm := preparedFormOf h00 D e
  transport := preparedFormOf_transport h00 D e
  preparedContraction :=
    ⟨{ arity := S₂.arity
       rvTarget := S₂.contracted
       program := twoStageProgram S₁ S₂
       rvForm := ρ
       factor := fun q => by
         obtain ⟨p, rfl⟩ := (prepOf_bijective h00 D e).surjective q
         rw [twoStageProgram_toMap, hfactor p, preparedFormOf_transport h00 D e p] },
      Classical.choice (exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ _
        (reindexedVFSet_properInvariant _ e (D.image_properInvariant h00 hc hκ hs hv)))⟩

theorem twoStage_headStage (S₁ : StandardContractionStage (G := G) (reindexedVFSet D.map.image e))
    (S₂ : StandardContractionStage (G := G) S₁.contracted)
    (ρ : Map S₂.contracted (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hfactor : ∀ p : A, (ρ (S₂.contraction (S₁.contraction (prepOf D e p)))).val = (ω p).val) :
    headStage (twoStage h00 hc linear hκ hs hv hsmall hΓ D S₁ S₂ ρ hfactor).preparedContraction.data.program = S₁ :=
  rfl

theorem twoStage_restProgram (S₁ : StandardContractionStage (G := G) (reindexedVFSet D.map.image e))
    (S₂ : StandardContractionStage (G := G) S₁.contracted)
    (ρ : Map S₂.contracted (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hfactor : ∀ p : A, (ρ (S₂.contraction (S₁.contraction (prepOf D e p)))).val = (ω p).val) :
    restProgram (twoStage h00 hc linear hκ hs hv hsmall hΓ D S₁ S₂ ρ hfactor).preparedContraction.data.program =
      .step S₂ (.zero S₂.contracted) :=
  rfl

theorem twoStage_volumeIndex (S₁ : StandardContractionStage (G := G) (reindexedVFSet D.map.image e))
    (S₂ : StandardContractionStage (G := G) S₁.contracted)
    (ρ : Map S₂.contracted (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hfactor : ∀ p : A, (ρ (S₂.contraction (S₁.contraction (prepOf D e p)))).val = (ω p).val) (i : Fin 2) :
    (twoStage h00 hc linear hκ hs hv hsmall hΓ D S₁ S₂ ρ hfactor).preparedContraction.data.program.volumeIndex i =
      Fin.lastCases (S₂.oldLabels S₁.leading) (fun _ : Fin 1 => S₂.leading) i := by
  change (twoStageProgram S₁ S₂).volumeIndex i = _
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.lastCases_last]
    change (OrderedStandardContractionProgram.step S₁ (.step S₂ (.zero S₂.contracted))).volumeIndex (Fin.last 1) = _
    rw [OrderedStandardContractionProgram.volumeIndex_step_last]
    rfl
  · rw [Fin.lastCases_castSucc]
    change (OrderedStandardContractionProgram.step S₁ (.step S₂ (.zero S₂.contracted))).volumeIndex j.castSucc = _
    rw [OrderedStandardContractionProgram.volumeIndex_step_castSucc, Fin.fin_one_eq_zero j]
    change (OrderedStandardContractionProgram.step S₂ (.zero S₂.contracted)).volumeIndex (Fin.last 0) = _
    rw [OrderedStandardContractionProgram.volumeIndex_step_last]
    rfl

end DiamondIntegral.Section7.TwoStageContractions
