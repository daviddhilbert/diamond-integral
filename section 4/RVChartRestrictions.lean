import «section 4».RVChartDisjointUnion
import «section 4».RVChartUnionProperties

/-! Restrict actual RV objects to original-base definable pieces. Their
coordinate maps and partial volumes are retained; finite RES patterns and
bounded domains are preserved. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVChartRestrictions
open RVMeasuredCharts RVMeasuredBounds RVChartDisjointUnion RVCoordinateMaps FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def restrict {B : Base (M := M)} {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (hsub : I ⊆ a.domain) : Data B n k where
  domain := I
  domain_definable := hI
  coordinate := a.coordinate
  coordinate_definable := by
    have h := a.coordinate_definable.inter (hI.preimage_real (fun _ : Fin (k + n) => .rv) (headIndex k n))
    convert h using 1
    ext w
    change (w ∘ headIndex k n ∈ I ∧ a.coordinate (w ∘ headIndex k n) = w ∘ tailIndex k n) ↔
      (w ∘ headIndex k n ∈ a.domain ∧ a.coordinate (w ∘ headIndex k n) = w ∘ tailIndex k n) ∧
        w ∘ headIndex k n ∈ I ∧ w ∈ sortedUniverse (fun _ => .rv)
    constructor
    · rintro ⟨hi, he⟩
      have hg : w ∈ graphOn a.domain a.coordinate := ⟨hsub hi, he⟩
      exact ⟨hg, hi, a.coordinate_definable.proper w hg⟩
    · exact fun h => ⟨h.2.1, h.1.2⟩
  coordinate_proper := fun u hu => a.coordinate_proper u (hsub hu)
  finite_fibres := fun t => (a.finite_fibres t).subset (fun _ h => ⟨hsub h.1, h.2⟩)
  volume := a.volume
  volume_definable := by
    have h := a.volume_definable.inter (hI.preimage_real (fun _ : Fin (n + 1) => .rv) Fin.succ)
    convert h using 1
    ext w
    change (Fin.tail w ∈ I ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = a.volume (Fin.tail w)) ↔
      (Fin.tail w ∈ a.domain ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = a.volume (Fin.tail w)) ∧
        Fin.tail w ∈ I ∧ w ∈ sortedUniverse (fun _ => .rv)
    constructor
    · rintro ⟨hi, h0, he⟩
      have hg : w ∈ {w : Fin (n + 1) → M | Fin.tail w ∈ a.domain ∧
          NonzeroRV (w 0) ∧ codeValue (w 0) = a.volume (Fin.tail w)} := ⟨hsub hi, h0, he⟩
      exact ⟨hg, hi, a.volume_definable.proper w hg⟩
    · exact fun h => ⟨h.2.1, h.1.2⟩

theorem restrict_weight {B : Base (M := M)} {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (hsub : I ⊆ a.domain) (u : Fin n → M) :
    (restrict a I hI hsub).toChart.correctedWeight u = a.toChart.correctedWeight u := rfl

theorem restrict_finite_patterns {B : Base (M := M)} {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (hsub : I ⊆ a.domain)
    (ha : (Set.range a.toChart.valuePattern).Finite) :
    (Set.range (restrict a I hI hsub).toChart.valuePattern).Finite := by
  apply ha.subset
  rintro p ⟨u, rfl⟩
  exact ⟨⟨u.val, hsub u.property⟩, rfl⟩

theorem restrict_domain_bounded {B : Base (M := M)} {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (hsub : I ⊆ a.domain)
    (ha : DomainBounded a.toChart) : DomainBounded (restrict a I hI hsub).toChart := by
  obtain ⟨β, hβ⟩ := ha
  exact ⟨β, fun u hu i hi => hβ u (hsub hu) i hi⟩

theorem difference_definable (B : Base (M := M)) {n : ℕ} (A I : Set (Fin n → M))
    (hA : DefinableOverBase B (fun _ : Fin n => .rv) A)
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) :
    DefinableOverBase B (fun _ : Fin n => .rv) (A \ I) := by
  have h := hA.inter hI.compl
  convert h using 1
  ext u
  change (u ∈ A ∧ u ∉ I) ↔ u ∈ A ∧ u ∈ sortedUniverse (fun _ => .rv) ∧ u ∉ I
  exact ⟨fun hu => ⟨hu.1, hA.proper u hu.1, hu.2⟩, fun hu => ⟨hu.1, hu.2.2⟩⟩

def outside {B : Base (M := M)} {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) : Data B n k :=
  restrict a (a.domain \ I) (difference_definable B a.domain I a.domain_definable hI) (fun _ h => h.1)

def inside {B : Base (M := M)} {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) : Data B n k :=
  restrict a (a.domain ∩ I) (a.domain_definable.inter hI) (fun _ h => h.1)

theorem pieces_disjoint {B : Base (M := M)} {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) : Disjoint (outside a I hI).domain (inside a I hI).domain := by
  apply Set.disjoint_left.mpr
  intro u hu hv
  exact hu.2 hv.2

def partitionIso {B : Base (M := M)} {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) :
    Iso (disjointUnion (outside a I hI) (inside a I hI) (pieces_disjoint a I hI)).toChart a.toChart := by
  apply coordinateIso _ _ (id : Fin n → Fin n)
  · refine ⟨?_, (fun _ _ _ _ h => h), ?_⟩
    · intro u hu
      exact hu.elim (fun h => h.1) (fun h => h.1)
    · intro y hy
      by_cases hi : y ∈ I
      · exact ⟨y, Or.inr ⟨hy, hi⟩, rfl⟩
      · exact ⟨y, Or.inl ⟨hy, hi⟩, rfl⟩
  · intro u _
    change piecewise (a.domain \ I) a.volume a.volume u *
      (∏ i, codeValue (piecewise (a.domain \ I) a.coordinate a.coordinate u i)) = a.toChart.correctedWeight u
    simp only [piecewise, ite_self]
    rfl

end DiamondIntegral.Section4.RVChartRestrictions
