import «section 3».RVDNFRelabel
import Section3.GuardedRationalNormalForm
import Section4.RVCoordinates
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def allRVVariableEquiv (n : ℕ) : RVVariableSlot (fun _ : Fin n => SortTag.rv) ≃ Fin n where
  toFun := Subtype.val
  invFun i := ⟨i,rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

def sourceVFFixedValues (p : Parameters S) (n : ℕ) : VFSlot p.sorts (fun _ : Fin n => .rv) → VFType (M := M) :=
  SourceAssignment.vfValues p.sorts (fun _ : Fin n => .rv) p.values (fun _ => iRVOne) p.sorted
    (fun _ => rv_one_mem hM)

def sourceRVFixedParameters (p : Parameters S) : RVParameterSlot p.sorts → CanonicalRV.RVSort M :=
  SourceAssignment.rvParameters p.sorts p.values p.sorted

theorem sourceVF_allRV_independent (p : Parameters S) (z : Fin n → M)
    (hz : ∀ i, sortEval SortTag.rv (z i)) :
    SourceAssignment.vfValues p.sorts (fun _ : Fin n => .rv) p.values z p.sorted hz = sourceVFFixedValues p n := by
  funext i
  apply Subtype.ext
  rcases i with ⟨i,hi⟩
  cases i with
  | inl j => rfl
  | inr j => cases hi

/-- The checked source normal form is transported to literal RV coordinate
indices with the same parameter package and all domain certificates. -/
theorem definableRV_guarded_DNF {A : Set (Fin n → M)} (hA : DefinableOver S (fun _ => .rv) A) :
    ∃ p : Parameters S,
    ∃ D : LiteralDNF (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n),
      ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ,
        ((rvValues (fun i => (x i : CanonicalRV.RVSort M))) ∈ A ↔
          PolarityDNF.holds (RVLiteral.comparison (sourceVFFixedValues p n) (sourceRVFixedParameters p)
            (fun i => (x i : CanonicalRV.RVSort M))) D) ∧
        LiteralDNF.Certified (sourceVFFixedValues p n) (sourceRVFixedParameters p)
          (fun i => (x i : CanonicalRV.RVSort M)) D := by
  obtain ⟨p,φ,hφ,he⟩ := hA
  obtain ⟨D,hD⟩ := model_uniform_raw_normal_form p.sorts (fun _ : Fin n => .rv) φ hφ
  let f := allRVVariableEquiv n
  refine ⟨p,rvDNFRelabel f D,?_⟩
  intro x
  let z : Fin n → M := rvValues (fun i => (x i : CanonicalRV.RVSort M))
  have hz : ∀ i, sortEval SortTag.rv (z i) := fun i => (x i).val.property
  have hn := hD M p.values z p.sorted hz
  have hvf := sourceVF_allRV_independent p z hz
  have hrv : SourceAssignment.rvVariables (fun _ : Fin n => .rv) z hz =
      (fun i => (x (f i) : CanonicalRV.RVSort M)) := by
    funext i
    apply Subtype.ext
    rfl
  rw [hvf,hrv] at hn
  have hm : z ∈ A ↔ φ.Realize p.values z := by
    rw [he]
    exact and_iff_right hz
  have hr := rvDNFRelabel_comparison f D (sourceVFFixedValues p n) (sourceRVFixedParameters p)
    (fun i => (x i : CanonicalRV.RVSort M))
  exact ⟨hm.trans (hn.1.trans hr.symm),rvDNFRelabel_certified f D _ _ _ hn.2⟩
end DiamondIntegral.Section3
