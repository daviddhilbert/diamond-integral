import «section 3».GammaGroundFiniteValuePoints
import «section 3».FullGammaFunctionMaps
import «section 3».GammaGroundFormTotalization
import «section 4».GammaWeightedCharts

/-! The two Gamma predicate syntaxes describe the same complete RV code
sets over the unchanged real/Gamma base. Total Gamma function graphs
agree after the explicit output-coordinate permutation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaCodeBridge
open GammaOrderLogic GammaDefinableMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem full_iff {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) :
    FullGammaSyntax.Definable (integrationGammaBase B) (fun γ => γ ∈ I) ↔ GammaDefinable B I :=
  (integrationGammaDefinable_iff (fun _ hz i => (hz.1 i).1)).symm

theorem native_iff {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) :
    GammaGroundDefinable hc B ((volumeGammaSpace hc).power (Fin n)) I ↔ GammaDefinable B I :=
  (gammaGroundGammaPower_definable_iff I).trans (full_iff I)

def native (hc : CanonicalStructure.IsCanonical (M := M)) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) : GammaGroundGammaPiece hc B n :=
  ⟨I, (native_iff I).mpr hI⟩

theorem function_iff {n : ℕ} (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) :
    FullGammaFunction (integrationGammaBase B) f ↔ MapDefinable B f := by
  let α : Fin n ⊕ Fin 1 → Fin (n + 1) := Sum.elim Fin.succ (fun _ => 0)
  let β : Fin (n + 1) → Fin n ⊕ Fin 1 := Fin.cases (.inr 0) Sum.inl
  constructor
  · intro hf
    apply (full_iff _).mp
    exact (FullGammaSyntax.Definable.reindex hf α).congr (fun _ => eq_comm)
  · intro hf
    have hh := ((full_iff _).mpr hf).reindex β
    exact hh.congr (fun _ => eq_comm)

def form (hc : CanonicalStructure.IsCanonical (M := M)) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : MapDefinable B f) :
    GammaGroundVolumeForm hc B (native hc I hI) :=
  (fullGammaFunctionMap f ((function_iff f).mpr hf)).restrict (fun _ _ => Set.mem_univ _)

theorem form_value {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : MapDefinable B f)
    (a : native hc I hI) : gammaGroundFormValue (form hc I hI f hf) a = f a.val := rfl

end DiamondIntegral.Section4.Section3GammaCodeBridge
