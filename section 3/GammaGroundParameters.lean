import «section 3».ImaginaryParameterChange
import «section 3».PowerProjectionMaps
import «section 3».GammaVolumeForms

/-! Definability over a real base and an arbitrary collection of actual
Gamma names. Each defining formula uses finitely many of those names;
Boolean operations join the tuples and keep every RV code in the graph. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {B : GammaParameters.Base (M := M)} {Q : Space LRV M}

def GammaGroundDefinable (hc : CanonicalStructure.IsCanonical (M := M))
    (B : GammaParameters.Base (M := M)) (Q : Space LRV M) (A : Set Q.Carrier) : Prop :=
  ∃ k, ∃ γ : Fin k → Values.Gamma (M := M), (∀ i, γ i ∈ B.gamma) ∧
    ImaginaryDefinable ((volumeGammaSpace hc).power (Fin k)) γ Q B.real A

theorem gammaGroundNames_append {k l : ℕ} {γ : Fin k → Values.Gamma (M := M)}
    {δ : Fin l → Values.Gamma (M := M)} (hγ : ∀ i, γ i ∈ B.gamma) (hδ : ∀ i, δ i ∈ B.gamma) :
    ∀ i, Fin.append γ δ i ∈ B.gamma := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simpa only [Fin.append_left] using hγ a
  · simpa only [Fin.append_right] using hδ b

theorem gammaPowerProjection_left_append (S : Set M) (k l : ℕ)
    (γ : Fin k → Values.Gamma (M := M)) (δ : Fin l → Values.Gamma (M := M)) :
    ((universalPowerProjection (volumeGammaSpace hc) S (Fin.castAdd l)).toFun
      ⟨Fin.append γ δ, Set.mem_univ _⟩).val = γ := by
  funext i
  change Fin.append γ δ (Fin.castAdd l i) = γ i
  rw [Fin.append_left]

theorem gammaPowerProjection_right_append (S : Set M) (k l : ℕ)
    (γ : Fin k → Values.Gamma (M := M)) (δ : Fin l → Values.Gamma (M := M)) :
    ((universalPowerProjection (volumeGammaSpace hc) S (Fin.natAdd k)).toFun
      ⟨Fin.append γ δ, Set.mem_univ _⟩).val = δ := by
  funext i
  change Fin.append γ δ (Fin.natAdd k i) = δ i
  rw [Fin.append_right]

theorem GammaGroundDefinable.of_real {A : Set Q.Carrier} (hA : Q.Definable B.real A) :
    GammaGroundDefinable hc B Q A :=
  ⟨0, Fin.elim0, fun i => i.elim0, ImaginaryDefinable.of_real hA⟩

theorem GammaGroundDefinable.inter {A D : Set Q.Carrier}
    (hA : GammaGroundDefinable hc B Q A) (hD : GammaGroundDefinable hc B Q D) :
    GammaGroundDefinable hc B Q (A ∩ D) := by
  obtain ⟨k, γ, hγ, hA⟩ := hA
  obtain ⟨l, δ, hδ, hD⟩ := hD
  refine ⟨k + l, Fin.append γ δ, gammaGroundNames_append hγ hδ, ?_⟩
  have hA' := hA.changeName (universalPowerProjection (volumeGammaSpace hc) B.real (Fin.castAdd l))
    (gammaPowerProjection_left_append B.real k l γ δ)
  have hD' := hD.changeName (universalPowerProjection (volumeGammaSpace hc) B.real (Fin.natAdd k))
    (gammaPowerProjection_right_append B.real k l γ δ)
  exact hA'.inter hD'

theorem GammaGroundDefinable.union {A D : Set Q.Carrier}
    (hA : GammaGroundDefinable hc B Q A) (hD : GammaGroundDefinable hc B Q D) :
    GammaGroundDefinable hc B Q (A ∪ D) := by
  obtain ⟨k, γ, hγ, hA⟩ := hA
  obtain ⟨l, δ, hδ, hD⟩ := hD
  refine ⟨k + l, Fin.append γ δ, gammaGroundNames_append hγ hδ, ?_⟩
  have hA' := hA.changeName (universalPowerProjection (volumeGammaSpace hc) B.real (Fin.castAdd l))
    (gammaPowerProjection_left_append B.real k l γ δ)
  have hD' := hD.changeName (universalPowerProjection (volumeGammaSpace hc) B.real (Fin.natAdd k))
    (gammaPowerProjection_right_append B.real k l γ δ)
  exact hA'.union hD'

theorem GammaGroundDefinable.compl {A : Set Q.Carrier} (hA : GammaGroundDefinable hc B Q A) :
    GammaGroundDefinable hc B Q Aᶜ := by
  obtain ⟨k, γ, hγ, hA⟩ := hA
  exact ⟨k, γ, hγ, hA.compl⟩

theorem GammaGroundDefinable.congr {A D : Set Q.Carrier} (hA : GammaGroundDefinable hc B Q A)
    (h : ∀ x, x ∈ A ↔ x ∈ D) : GammaGroundDefinable hc B Q D := by
  obtain ⟨k, γ, hγ, hA⟩ := hA
  exact ⟨k, γ, hγ, hA.congr h⟩

theorem GammaGroundDefinable.preimage {R : Space LRV M} {A : Set R.Carrier}
    (hA : GammaGroundDefinable hc B R A)
    (f : Map (DefSet.univ Q B.real) (DefSet.univ R B.real)) :
    GammaGroundDefinable hc B Q {x | (f ⟨x, Set.mem_univ _⟩).val ∈ A} := by
  obtain ⟨k, γ, hγ, hA⟩ := hA
  exact ⟨k, γ, hγ, hA.preimage f⟩

theorem GammaGroundDefinable.image {R : Space LRV M} {A : Set Q.Carrier}
    (hA : GammaGroundDefinable hc B Q A)
    (f : Map (DefSet.univ Q B.real) (DefSet.univ R B.real)) :
    GammaGroundDefinable hc B R {y | ∃ x ∈ A, (f ⟨x, Set.mem_univ _⟩).val = y} := by
  obtain ⟨k, γ, hγ, hA⟩ := hA
  exact ⟨k, γ, hγ, hA.image f⟩

structure GammaGroundDefSet (hc : CanonicalStructure.IsCanonical (M := M))
    (B : GammaParameters.Base (M := M)) (Q : Space LRV M) where
  carrier : Set Q.Carrier
  definable : GammaGroundDefinable hc B Q carrier

instance gammaGroundDefSetCoeSort : CoeSort (GammaGroundDefSet hc B Q) (Type _) := ⟨fun A => ↥A.carrier⟩

end DiamondIntegral.Section3
