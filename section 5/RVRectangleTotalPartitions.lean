import «section 5».OriginalRVTotalFamilies
import «section 5».RVRectangleDecompositionSchemata
import «section 5».NativeRVSetArithmetic

/-! Valid original RV rectangle packages partition the entire native RV
family over its original RV base, retaining every parameter coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a : ℕ}

theorem RVRectangleDecompositionSchema.total_partition
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    {D : GammaDomainFormula B p a (fun _ => .rv)} (W : RVRectangleDecompositionSchema D)
    (hv : ∀ x : X, W.Valid hc (rvValues x.val)) :
    (∀ i j, i ≠ j → Disjoint (originalRVTotalFamily X (W.cells i).source).carrier
      (originalRVTotalFamily X (W.cells j).source).carrier) ∧
    ∀ u, u ∈ (originalRVTotalFamily X D).carrier ↔ ∃ i, u ∈ (originalRVTotalFamily X (W.cells i).source).carrier := by
  have hsplit (u : Fin (p+a) → CanonicalRV.RVSort M) :
      Fin.append (rvValues (u ∘ Fin.castAdd a)) (rvValues (u ∘ Fin.natAdd p)) = rvValues u := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [rvValues,Function.comp_def,Fin.append_left,Fin.append_right]
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro u hi hj
    obtain ⟨hx,hi⟩ := (originalRVTotalFamily_mem X (W.cells i).source u).mp hi
    obtain ⟨_,hj⟩ := (originalRVTotalFamily_mem X (W.cells j).source u).mp hj
    have hd := (hv ⟨u ∘ Fin.castAdd a,hx⟩).2.2.2 i j hij (rvValues (u ∘ Fin.natAdd p))
    rw [hsplit u] at hd
    exact hd ⟨hi,hj⟩
  · intro u
    constructor
    · intro hu
      obtain ⟨hx,hu⟩ := (originalRVTotalFamily_mem X D u).mp hu
      have hc := (hv ⟨u ∘ Fin.castAdd a,hx⟩).2.2.1 (rvValues (u ∘ Fin.natAdd p))
      rw [hsplit u] at hc
      obtain ⟨i,hi⟩ := hc.mp hu
      exact ⟨i,(originalRVTotalFamily_mem X (W.cells i).source u).mpr ⟨hx,hi⟩⟩
    · rintro ⟨i,hu⟩
      obtain ⟨hx,hu⟩ := (originalRVTotalFamily_mem X (W.cells i).source u).mp hu
      have hc := (hv ⟨u ∘ Fin.castAdd a,hx⟩).2.2.1 (rvValues (u ∘ Fin.natAdd p))
      rw [hsplit u] at hc
      exact (originalRVTotalFamily_mem X D u).mpr ⟨hx,hc.mpr ⟨i,hu⟩⟩

end DiamondIntegral.Section5
