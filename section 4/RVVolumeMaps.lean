import «section 4».RVMeasuredCharts
import «section 4».GammaGroupNames

/-! Products of partial Gamma volume forms on actual RV domains. Auxiliary
Gamma values are represented by full RV-code fibres and eliminated by real
coordinate projection, preserving the original parameter base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVVolumeMaps

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def volumeGraph {n : ℕ} (I : Set (Fin n → M)) (μ : (Fin n → M) → Values.Gamma (M := M)) :
    Set (Fin (n + 1) → M) :=
  {w | Fin.tail w ∈ I ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = μ (Fin.tail w)}

def VolumeDefinable (B : Base (M := M)) {n : ℕ} (I : Set (Fin n → M))
    (μ : (Fin n → M) → Values.Gamma (M := M)) : Prop :=
  DefinableOverBase B (fun _ : Fin (n + 1) => .rv) (volumeGraph I μ)

theorem multiply_definable (B : Base (M := M)) {n : ℕ} (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I)
    (μ ν : (Fin n → M) → Values.Gamma (M := M))
    (hμ : VolumeDefinable B I μ) (hν : VolumeDefinable B I ν) :
    VolumeDefinable B I (fun z => μ z * ν z) := by
  let s : Fin n → Fin (n + 3) := fun i => i.succ.succ.succ
  let i1 : Fin (n + 3) := (0 : Fin (n + 2)).succ
  let i2 : Fin (n + 3) := (0 : Fin (n + 1)).succ.succ
  let δμ : Fin (n + 1) → Fin (n + 3) := Fin.cases 0 s
  let δν : Fin (n + 1) → Fin (n + 3) := Fin.cases i1 s
  let δm : Fin 3 → Fin (n + 3) := ![0, i1, i2]
  let π : Fin (n + 1) → Fin (n + 3) := fun i => i.succ.succ
  let G : Set (Fin 3 → M) :=
    {w | Proper w ∧ codeValue (w 0) * codeValue (w 1) = codeValue (w 2)}
  have hG : DefinableOverBase B (fun _ : Fin 3 => .rv) G := GammaGroupNames.mul_graph_definable_base B
  let U : Set (Fin (n + 3) → M) :=
    {w | w ∘ δμ ∈ volumeGraph I μ ∧ w ∈ sortedUniverse (fun _ => .rv)}
  let V : Set (Fin (n + 3) → M) :=
    {w | w ∘ δν ∈ volumeGraph I ν ∧ w ∈ sortedUniverse (fun _ => .rv)}
  let W : Set (Fin (n + 3) → M) :=
    {w | w ∘ δm ∈ G ∧ w ∈ sortedUniverse (fun _ => .rv)}
  let R := (U ∩ V) ∩ W
  have hR : DefinableOverBase B (fun _ : Fin (n + 3) => .rv) R :=
    ((hμ.preimage_real (fun _ => .rv) δμ).inter (hν.preimage_real (fun _ => .rv) δν)).inter
      (hG.preimage_real (fun _ => .rv) δm)
  have hImage : DefinableOverBase B (fun _ : Fin (n + 1) => .rv) ((fun w => w ∘ π) '' R) :=
    hR.image_real π
  have he : volumeGraph I (fun z => μ z * ν z) = (fun w => w ∘ π) '' R := by
    ext z
    constructor
    · rintro ⟨hz, h0, hv⟩
      obtain ⟨a, ha, hav⟩ := EndpointLogic.codeValue_surjective (μ (Fin.tail z))
      obtain ⟨b, hb, hbv⟩ := EndpointLogic.codeValue_surjective (ν (Fin.tail z))
      let w : Fin (n + 3) → M := Fin.cons a (Fin.cons b z)
      have hzs : z ∈ sortedUniverse (fun _ => .rv) := by
        intro i
        exact Fin.cases h0.1 (fun j => hI.proper _ hz j) i
      have hws : w ∈ sortedUniverse (fun _ => .rv) := by
        intro i
        exact Fin.cases ha.1 (Fin.cases hb.1 hzs) i
      have hm : w ∘ δμ ∈ volumeGraph I μ := by
        change Fin.tail z ∈ I ∧ NonzeroRV a ∧ codeValue a = μ (Fin.tail z)
        exact ⟨hz, ha, hav⟩
      have hn : w ∘ δν ∈ volumeGraph I ν := by
        change Fin.tail z ∈ I ∧ NonzeroRV b ∧ codeValue b = ν (Fin.tail z)
        exact ⟨hz, hb, hbv⟩
      have hp : w ∘ δm ∈ G := by
        have hw : w ∘ δm = ![a, b, z 0] := by
          funext i
          fin_cases i <;> rfl
        rw [hw]
        change Proper ![a, b, z 0] ∧ codeValue a * codeValue b = codeValue (z 0)
        refine ⟨?_, ?_⟩
        · intro i
          fin_cases i
          · exact ha
          · exact hb
          · exact h0
        · rw [hav, hbv]
          exact hv.symm
      exact ⟨w, ⟨⟨⟨hm, hws⟩, hn, hws⟩, hp, hws⟩, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      have hm : w ∘ δμ ∈ volumeGraph I μ := hw.1.1.1
      have hn : w ∘ δν ∈ volumeGraph I ν := hw.1.2.1
      have hp : w ∘ δm ∈ G := hw.2.1
      have hsrc : (fun i : Fin n => w (s i)) = Fin.tail z := funext (fun i => congrFun hwz i.succ)
      change (fun i => w (s i)) ∈ I ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = μ (fun i => w (s i)) at hm
      change (fun i => w (s i)) ∈ I ∧ NonzeroRV (w i1) ∧ codeValue (w i1) = ν (fun i => w (s i)) at hn
      rw [hsrc] at hm hn
      have hc : w i2 = z 0 := congrFun hwz 0
      have hpc : NonzeroRV (w i2) := hp.1 (2 : Fin 3)
      refine ⟨hm.1, hc ▸ hpc, ?_⟩
      change codeValue (z 0) = μ (Fin.tail z) * ν (Fin.tail z)
      calc
        codeValue (z 0) = codeValue (w i2) := congrArg codeValue hc.symm
        _ = codeValue (w 0) * codeValue (w i1) := hp.2.symm
        _ = μ (Fin.tail z) * ν (Fin.tail z) := congrArg₂ (· * ·) hm.2.2 hn.2.2
  change DefinableOverBase B (fun _ : Fin (n + 1) => .rv) (volumeGraph I (fun z => μ z * ν z))
  rw [he]
  exact hImage

theorem reindex_restrict_definable (B : Base (M := M)) {n m : ℕ}
    (I : Set (Fin n → M)) (J : Set (Fin m → M))
    (hJ : DefinableOverBase B (fun _ : Fin m => .rv) J)
    (μ : (Fin n → M) → Values.Gamma (M := M)) (hμ : VolumeDefinable B I μ)
    (π : Fin n → Fin m) (hJI : ∀ z ∈ J, z ∘ π ∈ I) :
    VolumeDefinable B J (fun z => μ (z ∘ π)) := by
  let ρ : Fin (n + 1) → Fin (m + 1) := Fin.cases 0 (fun i => (π i).succ)
  have h := (hμ.preimage_real (fun _ : Fin (m + 1) => .rv) ρ).inter
    (hJ.preimage_real (fun _ : Fin (m + 1) => .rv) Fin.succ)
  change DefinableOverBase B (fun _ : Fin (m + 1) => .rv) (volumeGraph J (fun z => μ (z ∘ π)))
  convert h using 1
  ext w
  change (Fin.tail w ∈ J ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = μ (Fin.tail w ∘ π)) ↔
    ((Fin.tail (w ∘ ρ) ∈ I ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = μ (Fin.tail (w ∘ ρ))) ∧
      w ∈ sortedUniverse (fun _ => .rv)) ∧
      (Fin.tail w ∈ J ∧ w ∈ sortedUniverse (fun _ => .rv))
  have ht : Fin.tail (w ∘ ρ) = Fin.tail w ∘ π := by funext i; rfl
  rw [ht]
  constructor
  · rintro ⟨hw, h0, he⟩
    have hs : w ∈ sortedUniverse (fun _ => .rv) := by
      intro i
      exact Fin.cases h0.1 (fun j => hJ.proper _ hw j) i
    exact ⟨⟨⟨hJI _ hw, h0, he⟩, hs⟩, hw, hs⟩
  · rintro ⟨⟨⟨_, h0, he⟩, _⟩, hw, _⟩
    exact ⟨hw, h0, he⟩

end DiamondIntegral.Section4.RVVolumeMaps
