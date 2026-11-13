import «section 4».Section3RVCodeBridge
import «section 3».GammaGroundMeasuredRVCategories
import «section 3».RVUnitGammaFormGraph

/-! Partial Gamma volume forms use all RV representatives in both APIs.
The following conversions retain the entire code graph and original base. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3RVFormBridge
open Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def rawForm {n : ℕ} {D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    (ω : GammaGroundVolumeForm hc B D) (x : Fin n → M) : Values.Gamma (M := M) :=
  if hx : x ∈ rawDomain D then (ω ((rawEquiv D).symm ⟨x, hx⟩)).val else 1

theorem rawForm_apply {n : ℕ} {D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    (ω : GammaGroundVolumeForm hc B D) (a : D) : rawForm ω (rvValues a.val) = (ω a).val := by
  have hx : rvValues a.val ∈ rawDomain D := ⟨a.val, a.property, rfl⟩
  simp only [rawForm, dif_pos hx]
  have he : (⟨rvValues a.val, hx⟩ : rawDomain D) = rawEquiv D a := rfl
  rw [he, Equiv.symm_apply_apply]

def codeGraph {n : ℕ} (A : Set (Fin n → M)) (w : (Fin n → M) → Values.Gamma (M := M)) :
    Set (Fin (n + 1) → M) :=
  {z | Fin.tail z ∈ A ∧ NonzeroRV (z 0) ∧ codeValue (z 0) = w (Fin.tail z)}

theorem rawForm_definable {n : ℕ} {D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    (ω : GammaGroundVolumeForm hc B D) :
    DefinableOverBase B (fun _ : Fin (n + 1) => .rv) (codeGraph (rawDomain D) (rawForm ω)) := by
  let π : Fin n ⊕ Fin 1 → Fin (n + 1) := Sum.elim Fin.succ (fun _ => 0)
  have h := ω.raw_graph_definable.preimage_comp π
  have hh : GammaGroundRawDefinable hc B (codeGraph (rawDomain D) (rawForm ω)) := by
    apply h.congr
    intro z
    change (∃ hu, ∃ hv, ∃ a : D, a.val = (rawRVSpace n).decode ⟨_, hu⟩ ∧
      (ω a).val = (volumeGammaSpace hc).decode ⟨_, hv⟩) ↔
      (Fin.tail z ∈ rawDomain D ∧ NonzeroRV (z 0) ∧ codeValue (z 0) = rawForm ω (Fin.tail z))
    constructor
    · rintro ⟨hu, hv, a, ha, hω⟩
      have hr : rvValues a.val = Fin.tail z := by
        rw [ha, rvValues_decode]
        rfl
      have hval : (ω a).val = codeValue (z 0) :=
        hω.trans (gammaVolume_code_decode (hc := hc) ⟨_, hv⟩)
      refine ⟨⟨a.val, a.property, hr⟩, hv, ?_⟩
      rw [← hr, rawForm_apply]
      exact hval.symm
    · rintro ⟨hz, hγ, he⟩
      let a := (rawEquiv D).symm ⟨Fin.tail z, hz⟩
      have ha : rvValues a.val = Fin.tail z := rawEquiv_symm_value D ⟨Fin.tail z, hz⟩
      have hu : (z ∘ π) ∘ Sum.inl ∈ (rawRVSpace (M := M) n).domain := ⟨a.val, ha⟩
      have hv : (z ∘ π) ∘ Sum.inr ∈ (volumeGammaSpace hc).domain := hγ
      refine ⟨hu, hv, a, ?_, ?_⟩
      · apply rvValues_injective
        rw [rvValues_decode]
        exact ha
      · have hval : (ω a).val = codeValue (z 0) := by
          rw [← rawForm_apply ω a, ha]
          exact he.symm
        exact hval.trans (gammaVolume_code_decode (hc := hc) ⟨_, hv⟩).symm
  apply (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) ?_).mp hh
  rintro z ⟨hz, hγ, _⟩
  intro i
  exact Fin.cases hγ.1 (fun j => (rawDomain_definable D).proper _ hz j) i

def ofRawForm {n : ℕ} (A : Set (Fin n → M))
    (hA : DefinableOverBase B (fun _ : Fin n => .rv) A)
    (w : (Fin n → M) → Values.Gamma (M := M))
    (hw : DefinableOverBase B (fun _ : Fin (n + 1) => .rv) (codeGraph A w)) :
    GammaGroundVolumeForm hc B (ofRaw A hA) where
  toFun a := ⟨w (rvValues a.val), Set.mem_univ _⟩
  graph_definable := by
    let π : Fin (n + 1) → Fin n ⊕ Fin 1 := Fin.cases (.inr 0) Sum.inl
    have hraw := ((gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B)
      (fun z hz i => hw.proper z hz i)).mpr hw).preimage_comp π
    apply GammaGroundDefinable.of_real_codes
    change GammaGroundRawDefinable hc B (ι := Fin n ⊕ Fin 1) _
    apply hraw.congr
    intro z
    change ((Fin.tail (z ∘ π)) ∈ A ∧ NonzeroRV ((z ∘ π) 0) ∧
      codeValue ((z ∘ π) 0) = w (Fin.tail (z ∘ π))) ↔ _
    have ht : Fin.tail (z ∘ π) = z ∘ Sum.inl := rfl
    have h0 : (z ∘ π) 0 = z (.inr 0) := rfl
    rw [ht, h0]
    constructor
    · rintro ⟨hz, hγ, he⟩
      have hu : z ∘ Sum.inl ∈ (rawRVSpace (M := M) n).domain :=
        ⟨fun i => ⟨z (.inl i), hA.proper _ hz i⟩, rfl⟩
      have hv : z ∘ Sum.inr ∈ (volumeGammaSpace hc).domain := hγ
      let a : ofRaw (hc := hc) A hA := ⟨(rawRVSpace n).decode ⟨z ∘ Sum.inl, hu⟩, by
        change rvValues ((rawRVSpace n).decode ⟨z ∘ Sum.inl, hu⟩) ∈ A
        rw [rvValues_decode]
        exact hz⟩
      refine ⟨⟨hu, hv⟩, a, rfl, ?_⟩
      change w (rvValues a.val) = (volumeGammaSpace hc).decode ⟨z ∘ Sum.inr, hv⟩
      have hval : w (rvValues a.val) = codeValue (z (.inr 0)) := by
        simp only [a, rvValues_decode]
        exact he.symm
      exact hval.trans (gammaVolume_code_decode (hc := hc) ⟨_, hv⟩).symm
    · rintro ⟨⟨hu, hv⟩, a, ha, hω⟩
      change a.val = (rawRVSpace n).decode ⟨z ∘ Sum.inl, hu⟩ at ha
      have hr : rvValues a.val = z ∘ Sum.inl := by rw [ha, rvValues_decode]
      have hval : w (rvValues a.val) = codeValue (z (.inr 0)) :=
        hω.trans (gammaVolume_code_decode (hc := hc) ⟨_, hv⟩)
      exact ⟨hr ▸ a.property, hv, (congrArg w hr).symm.trans hval |>.symm⟩

theorem ofRawForm_value {n : ℕ} (A : Set (Fin n → M))
    (hA : DefinableOverBase B (fun _ : Fin n => .rv) A)
    (w : (Fin n → M) → Values.Gamma (M := M))
    (hw : DefinableOverBase B (fun _ : Fin (n + 1) => .rv) (codeGraph A w))
    (a : ofRaw (hc := hc) A hA) : (ofRawForm A hA w hw a).val = w (rvValues a.val) := rfl

end DiamondIntegral.Section4.Section3RVFormBridge
