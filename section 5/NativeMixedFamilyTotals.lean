import «section 5».NativeMixedSortedRealization
import «section 5».SortedTupleReindexing
import «section 5».MixedTotalCoordinates

/-! Actual original-Gamma total mixed families and full total bijections
are obtained from their literal row formulas. The old RV base coordinates
are retained as RV coordinates throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p q n r m s : ℕ}

theorem sortedReindexedDomain_mem_iff {a c : ℕ} (ρ : Fin a ≃ Fin c)
    (D : Set (Fin a → M)) (w : Fin c → M) :
    w ∈ sortedReindexedDomain ρ D ↔ w ∘ ρ ∈ D := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    simpa only [Function.comp_def,Equiv.symm_apply_apply] using hx
  · intro h
    refine ⟨w ∘ ρ,h,?_⟩
    funext i
    simp only [Function.comp_apply,Equiv.apply_symm_apply]

theorem mixedTotalPermutation_sort (p q n r : ℕ) :
    Fin.append (Fin.append (fun _ : Fin p => SortTag.vf) (fun _ : Fin q => .rv))
        (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv)) ∘ (mixedTotalPermutation p q n r).symm =
      Fin.append (fun _ : Fin (p+n) => .vf) (fun _ : Fin (q+r) => .rv) := by
  rw [mixedTotalPermutation_append]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      simp only [Fin.append_left,Fin.append_right]

def nativeMixedFamilyTotal (X : Set (Fin (p+q) → M))
    (hX : DefinableOverBase B (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) X)
    (D : Set (Fin ((p+q)+(n+r)) → M))
    (hD : DefinableOverBase B
      (Fin.append (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
        (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) D) :
    GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+n) (q+r)) :=
  nativeMixedOfRaw (sortedReindexedDomain (mixedTotalPermutation p q n r) (rawRowTotal X D)) (by
    simpa only [mixedTotalPermutation_sort] using
      sortedReindexedDomain_definable (mixedTotalPermutation p q n r) (originalSortedRowTotal_definable hX hD))

theorem nativeMixedFamilyTotal_domain (X : Set (Fin (p+q) → M))
    (hX : DefinableOverBase B (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) X)
    (D : Set (Fin ((p+q)+(n+r)) → M))
    (hD : DefinableOverBase B
      (Fin.append (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
        (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) D) :
    nativeMixedDomain (nativeMixedFamilyTotal (hc := hc) X hX D hD) =
      sortedReindexedDomain (mixedTotalPermutation p q n r) (rawRowTotal X D) :=
  nativeMixedDomain_ofRaw _ _

theorem nativeMixedFamilyTotal_mem (X : Set (Fin (p+q) → M))
    (hX : DefinableOverBase B (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) X)
    (D : Set (Fin ((p+q)+(n+r)) → M))
    (hD : DefinableOverBase B
      (Fin.append (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
        (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) D)
    (z : Fin p → Section2.VF M) (t : Fin q → CanonicalRV.RVSort M)
    (x : Fin n → Section2.VF M) (u : Fin r → CanonicalRV.RVSort M) :
    (Fin.append z x,Fin.append t u) ∈ (nativeMixedFamilyTotal (hc := hc) X hX D hD).carrier ↔
      Fin.append (vfValues z) (rvValues t) ∈ X ∧
        Fin.append (Fin.append (vfValues z) (rvValues t)) (Fin.append (vfValues x) (rvValues u)) ∈ D := by
  change nativeMixedCode (Fin.append z x,Fin.append t u) ∈ sortedReindexedDomain _ _ ↔ _
  rw [sortedReindexedDomain_mem_iff]
  have hcode : nativeMixedCode (Fin.append z x,Fin.append t u) =
      Fin.append (Fin.append (vfValues z) (rvValues t)) (Fin.append (vfValues x) (rvValues u)) ∘
        (mixedTotalPermutation p q n r).symm := by
    rw [mixedTotalPermutation_append]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
        simp only [nativeMixedCode,vfValues,rvValues,Fin.append_left,Fin.append_right]
  rw [hcode]
  have he : (Fin.append (Fin.append (vfValues z) (rvValues t)) (Fin.append (vfValues x) (rvValues u)) ∘
      (mixedTotalPermutation p q n r).symm) ∘ mixedTotalPermutation p q n r =
      Fin.append (Fin.append (vfValues z) (rvValues t)) (Fin.append (vfValues x) (rvValues u)) := by
    funext i
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
  rw [he]
  change (_ ∧ _) ↔ _
  have hb : Fin.append (Fin.append (vfValues z) (rvValues t)) (Fin.append (vfValues x) (rvValues u)) ∘
      Fin.castAdd (n+r) = Fin.append (vfValues z) (rvValues t) := funext (fun i => Fin.append_left _ _ i)
  rw [hb]

def nativeMixedFamilyTotalBijection (X : Set (Fin (p+q) → M))
    (hX : DefinableOverBase B (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) X)
    (D : Set (Fin ((p+q)+(n+r)) → M)) (E : Set (Fin ((p+q)+(m+s)) → M))
    (hD : DefinableOverBase B
      (Fin.append (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
        (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) D)
    (hE : DefinableOverBase B
      (Fin.append (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
        (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))) E)
    (H : GammaSortedBijectionChart B (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
      (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))
      (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv)))
    (hH : ∀ z ∈ X, H.valid D E z) :
    GammaGroundBijection (nativeMixedFamilyTotal (hc := hc) X hX D hD) (nativeMixedFamilyTotal X hX E hE) := by
  let F := sortedIsoReindex (gammaSortedTotalIso H hX hE hH)
    (mixedTotalPermutation p q n r) (mixedTotalPermutation p q m s)
  apply nativeMixedBijectionOfSortedIso
  rw [nativeMixedFamilyTotal_domain,nativeMixedFamilyTotal_domain]
  simpa only [mixedTotalPermutation_sort] using F

end DiamondIntegral.Section5
