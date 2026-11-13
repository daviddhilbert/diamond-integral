import «section 4».Section3GammaCodeFamilyBridge
import «section 4».GammaRVFamilyIsomorphisms
import «section 4».GammaOrdinaryFamilyIsomorphisms

/-! Actual original-base contracted native Gamma family isomorphisms
give the chart family isomorphisms, including the full volume equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaFamilyIsomorphismBridge
open Section3GammaChartBridge Section3GammaCodeFamilyBridge GammaRVChartPresentation FiniteFamilyBijections
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem sourcePiece_lift {n : ℕ} {A D : GammaGroundGammaObject hc B n} (f : GammaGroundGammaHom A D)
    (F : GammaGroundFamilyBijection A.codeLift D.codeLift)
    (hF : ∀ c, D.decode (F.equiv c) = f.bijection.equiv (A.decode c)) (i : Fin A.tags) (j : Fin D.tags) :
    sourcePiece (liftEquiv F) i j = sharp (sourcePiece (Section3GammaFamilyBridge.equiv f.bijection) i j) := by
  rw [sourcePiece_pullback (liftEquiv F) (Section3GammaFamilyBridge.equiv f.bijection) codeValues codeValues
    (fun _ _ h => h.2) (fun _ _ h => h.2) (contraction f F hF)]
  ext z
  change (z ∈ sharp (A.piece i).carrier ∧ codeValues z ∈ sourcePiece (Section3GammaFamilyBridge.equiv f.bijection) i j) ↔
    Proper z ∧ codeValues z ∈ sourcePiece (Section3GammaFamilyBridge.equiv f.bijection) i j
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, sourcePiece_subset _ i j h.2⟩, h.2⟩⟩

def ordinaryWithLift {n : ℕ} {A D : GammaGroundGammaObject hc B n} (f : GammaGroundGammaHom A D)
    (F : GammaGroundFamilyBijection A.codeLift D.codeLift)
    (hF : ∀ c, D.decode (F.equiv c) = f.bijection.equiv (A.decode c)) :
    GammaOrdinaryFamilyIsomorphisms.Iso (ordinaryFamily A) (ordinaryFamily D) where
  equiv := Section3GammaFamilyBridge.equiv f.bijection
  lift := liftEquiv F
  source_definable := Section3GammaFamilyBridge.sourcePiece_definable f.bijection
  target_definable i j := by
    change GammaOrderLogic.GammaDefinable B (sourcePiece (Section3GammaFamilyBridge.equiv f.bijection).symm j i)
    have he : (Section3GammaFamilyBridge.equiv f.bijection).symm =
        Section3GammaFamilyBridge.equiv f.bijection.symm := by
      simp only [Section3GammaFamilyBridge.equiv, GammaGroundFamilyBijection.symm, Equiv.symm_trans,
        Equiv.symm_symm, Equiv.trans_assoc]
    rw [he]
    exact Section3GammaFamilyBridge.sourcePiece_definable f.bijection.symm j i
  graph_definable := Section3GammaFamilyBridge.graph_definable f.bijection
  lift_definable i j := by
    have h := lift_graph F i j
    rw [sourcePiece_lift f F hF i j] at h
    have he : RVMeasuredCharts.graphOn (sharp (sourcePiece (Section3GammaFamilyBridge.equiv f.bijection) i j))
        (pieceMap (liftEquiv F) (fun _ => iRVZero) i) =
        rawGraphOn (sourcePiece (Section3GammaFamilyBridge.equiv f.bijection) i j)
          (pieceMap (liftEquiv F) (fun _ => iRVZero) i) := by
      ext w
      exact and_congr_right (fun _ => eq_comm)
    exact (congrArg (fun T => DefinableOverBase B (fun _ : Fin (n + n) => .rv) T) he).mp h
  contraction := contraction f F hF

def ordinary {n : ℕ} {A D : GammaGroundGammaObject hc B n} (f : GammaGroundGammaHom A D) :
    GammaOrdinaryFamilyIsomorphisms.Iso (ordinaryFamily A) (ordinaryFamily D) :=
  ordinaryWithLift f (Classical.choose f.contraction) (Classical.choose_spec f.contraction)

def measured {n : ℕ} {A D : GammaGroundMeasuredGammaObject hc B n} (f : GammaGroundMeasuredGammaHom A D) :
    GammaRVFamilyIsomorphisms.Iso (measuredFamily A) (measuredFamily D) where
  equiv := (ordinary f.underlying).equiv
  lift := (ordinary f.underlying).lift
  source_definable := (ordinary f.underlying).source_definable
  target_definable := (ordinary f.underlying).target_definable
  graph_definable := (ordinary f.underlying).graph_definable
  lift_definable := (ordinary f.underlying).lift_definable
  contraction := (ordinary f.underlying).contraction
  volume_eq p := by
    obtain ⟨u, rfl⟩ := (Section3GammaFamilyBridge.familyEquiv A.underlying).surjective p
    change (measuredFamily A u.1).volume u.2.val =
      (measuredFamily D (f.underlying.bijection.equiv u).1).volume (f.underlying.bijection.equiv u).2.val *
        (∏ i, cast (gammaCarrier hc) ((f.underlying.bijection.equiv u).2.val i)) /
          (∏ i, cast (gammaCarrier hc) (u.2.val i))
    apply (eq_div_iff_mul_eq').mpr
    have h := (measuredFamily_weight A u).trans
      ((f.preserves u).trans (measuredFamily_weight D (f.underlying.bijection.equiv u)).symm)
    exact h

end DiamondIntegral.Section4.Section3GammaFamilyIsomorphismBridge
