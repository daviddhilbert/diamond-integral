import «section 4».Section3GammaAffineInput
import «section 4».GammaFiniteFirstMatch

/-! Finite rational-affine normal forms give original-base definable
disjoint continuity partitions, simultaneously for finitely many maps.
Continuity is proved from the explicit rational-affine branch formula. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DiamondIntegral.Section4.GammaTopology

namespace DiamondIntegral.Section4.GammaContinuousPartitions
open GammaOrderLogic GammaDefinableMaps GammaRationalAffineContinuity GammaFiniteFirstMatch
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure Partition (B : Base (M := M)) (n : ℕ)
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) where
  size : ℕ
  domain : Fin size → Set (Fin n → Values.Gamma (M := M))
  definable : ∀ i, GammaDefinable B (domain i)
  disjoint : Pairwise (fun i j => Disjoint (domain i) (domain j))
  cover : ∀ x, ∃ i, x ∈ domain i
  continuous : ∀ i, ContinuousOn T (domain i)

def ofBranches (B : Base (M := M)) {n m : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hT : MapDefinable B T)
    (a : Fin m → Branch B n) (ha : ∀ x, ∃ i, T x = (a i).eval x) : Partition B n T where
  size := m
  domain := first (fun i => {x | T x = (a i).eval x})
  definable i := GammaFiniteFirstMatch.definable _
    (fun j => equal_maps_definable B _ _ hT (a j).definable) i
  disjoint := GammaFiniteFirstMatch.disjoint _
  cover x := (GammaFiniteFirstMatch.cover _ x).mp (ha x)
  continuous i := (a i).continuous.continuousOn.congr (fun _ hx => hx.1)

theorem exists_partition (B : Base (M := M)) (affine : Section3GammaAffineInput.Input B)
    {n : ℕ} (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : MapDefinable B T) : Nonempty (Partition B n T) := by
  obtain ⟨m, a, ha⟩ := affine n T hT
  exact ⟨ofBranches B T hT a ha⟩

structure CommonCover (B : Base (M := M)) (n N : ℕ)
    (T : Fin N → (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) where
  Index : Type
  finite : Finite Index
  domain : Index → Set (Fin n → Values.Gamma (M := M))
  definable : ∀ i, GammaDefinable B (domain i)
  disjoint : Pairwise (fun i j => Disjoint (domain i) (domain j))
  cover : ∀ x, ∃ i, x ∈ domain i
  continuous : ∀ i j, ContinuousOn (T j) (domain i)

def common (B : Base (M := M)) {n N : ℕ}
    (T : Fin N → (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (P : ∀ j, Partition B n (T j)) : CommonCover B n N T where
  Index := ∀ j, Fin (P j).size
  finite := inferInstance
  domain i := ⋂ j, (P j).domain (i j)
  definable i := GammaQuantifierLogic.finite_iInter_definable_base B _
    (fun j => (P j).definable (i j))
  disjoint := by
    intro i j hij
    obtain ⟨l, hl⟩ : ∃ l, i l ≠ j l := not_forall.mp (fun he => hij (funext he))
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp ((P l).disjoint hl)
      (Set.mem_iInter.mp hx l) (Set.mem_iInter.mp hy l)
  cover x := by
    choose i hi using (fun j => (P j).cover x)
    exact ⟨i, Set.mem_iInter.mpr hi⟩
  continuous i j := ((P j).continuous (i j)).mono (Set.iInter_subset _ j)

theorem exists_common (B : Base (M := M)) (affine : Section3GammaAffineInput.Input B)
    {n N : ℕ} (T : Fin N → (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : ∀ j, MapDefinable B (T j)) : Nonempty (CommonCover B n N T) := by
  let P (j : Fin N) := Classical.choice (exists_partition B affine (T j) (hT j))
  exact ⟨common B T P⟩

end DiamondIntegral.Section4.GammaContinuousPartitions
