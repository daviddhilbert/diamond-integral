import «section 4».GammaBoundaryGapLabels

/-! Every two distinct labels in the finite boundary stack family have
disjoint sets. A common gap point forces equal endpoint values, active
endpoint uniqueness forces equal labels, and point stacks lie on the
boundary while open stacks avoid it. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundaryStackDisjointness
open GammaOrderLogic GammaFiniteGraphPartition GammaGraphPartitionEndpoints GammaBoundaryStackFamily
open GammaBoundaryStacks GammaBoundaryStackBases GammaBoundaryGapLabels GammaCellSections
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem option_endpoint_injective {A : Set (Fin (n + 1) → Values.Gamma (M := M))}
    (P : FiniteGraphPartition B A) (y : Fin n → Values.Gamma (M := M)) (a b : Option (Fin P.size))
    (ha : ∀ i, a = some i → y ∈ P.domain i) (hb : ∀ i, b = some i → y ∈ P.domain i)
    (he : a.map (fun i => endpoint P i y) = b.map (fun i => endpoint P i y)) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j => cases he
  | some i =>
    cases b with
    | none => cases he
    | some j =>
      apply congrArg some
      exact endpoint_injective P y i j (ha i rfl) (hb j rfl) (Option.some.inj he)

theorem gap_stacks_disjoint (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (q q' : GapLabel P.size) (hne : q ≠ q') :
    Disjoint (stack R P (gapLabel q)) (stack R P (gapLabel q')) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hs := stack_gap R P q z hz
  have hs' := stack_gap R P q' z hz'
  have hv := valid_gap R P q (Fin.tail z) hs.1
  have hv' := valid_gap R P q' (Fin.tail z) hs'.1
  have he := OrderGapComponents.endpoints_eq_of_inter _ _ _ _ _ hv hv' (z 0) hs.2 hs'.2
  have hd := (gapSource_iff R P q (Fin.tail z)).mp (base_source R P q (Fin.tail z) hs.1)
  have hd' := (gapSource_iff R P q' (Fin.tail z)).mp (base_source R P q' (Fin.tail z) hs'.1)
  exact hne (Prod.ext
    (option_endpoint_injective P (Fin.tail z) q.1 q'.1 hd.1 hd'.1 he.1)
    (option_endpoint_injective P (Fin.tail z) q.2 q'.2 hd.2 hd'.2 he.2))

theorem point_stack_spec (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (i : Fin P.size)
    (z : Fin (n + 1) → Values.Gamma (M := M)) (hz : z ∈ stack R P (.inl i)) :
    Fin.tail z ∈ P.domain i ∧ z 0 = endpoint P i (Fin.tail z) := by
  change Fin.tail z ∈ pointBase R (P.domain i) (endpoint P i) ∧ z 0 = endpoint P i (Fin.tail z) at hz
  obtain ⟨t, htR, htC, ht⟩ := (mem_fibreBase _ (Fin.tail z)).mp hz.1
  exact ⟨htC, hz.2⟩

theorem point_stack_boundary (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (i : Fin P.size)
    (z : Fin (n + 1) → Values.Gamma (M := M)) (hz : z ∈ stack R P (.inl i)) :
    z ∈ GammaFamilyBoundary.Boundary R := by
  obtain ⟨hy, he⟩ := point_stack_spec R P i z hz
  have hb := endpoint_mem P i (Fin.tail z) hy
  have hez : Fin.cons (endpoint P i (Fin.tail z)) (Fin.tail z) = z :=
    (congrArg (fun t => Fin.cons t (Fin.tail z)) he.symm).trans (Fin.cons_self_tail z)
  exact hez ▸ hb

theorem point_stacks_disjoint (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (i j : Fin P.size) (hne : i ≠ j) :
    Disjoint (stack R P (.inl i)) (stack R P (.inl j)) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨hi, he⟩ := point_stack_spec R P i z hz
  obtain ⟨hj, he'⟩ := point_stack_spec R P j z hz'
  exact hne (endpoint_injective P (Fin.tail z) i j hi hj (he.symm.trans he'))

theorem point_gap_disjoint (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (i : Fin P.size) (q : GapLabel P.size) :
    Disjoint (stack R P (.inl i)) (stack R P (gapLabel q)) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hs := stack_gap R P q z hz'
  have hv := valid_gap R P q (Fin.tail z) hs.1
  have hb : Fin.cons (z 0) (Fin.tail z) ∈ GammaFamilyBoundary.Boundary R := by
    simpa only [Fin.cons_self_tail] using point_stack_boundary R P i z hz
  exact hv.no_boundary (z 0) hb hs.2

def unpackGap {N : ℕ} : ((Fin N × Fin N) ⊕ (Fin N ⊕ (Fin N ⊕ Unit))) → GapLabel N
  | .inl (i, j) => (some i, some j)
  | .inr (.inl i) => (some i, none)
  | .inr (.inr (.inl j)) => (none, some j)
  | .inr (.inr (.inr _)) => (none, none)

theorem gapLabel_unpack {N : ℕ} (s : ((Fin N × Fin N) ⊕ (Fin N ⊕ (Fin N ⊕ Unit)))) :
    gapLabel (unpackGap s) = .inr s := by
  rcases s with ⟨i, j⟩ | (i | (j | u))
  · rfl
  · rfl
  · rfl
  · cases u
    rfl

theorem pairwise_disjoint (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) :
    Pairwise (fun i j : Label P.size => Disjoint (stack R P i) (stack R P j)) := by
  intro i j hne
  rcases i with i | s <;> rcases j with j | t
  · exact point_stacks_disjoint R P i j (fun he => hne (congrArg Sum.inl he))
  · simpa only [gapLabel_unpack] using point_gap_disjoint R P i (unpackGap t)
  · simpa only [gapLabel_unpack] using (point_gap_disjoint R P j (unpackGap s)).symm
  · have hq : unpackGap s ≠ unpackGap t := by
      intro he
      exact hne ((gapLabel_unpack s).symm.trans ((congrArg gapLabel he).trans (gapLabel_unpack t)))
    simpa only [gapLabel_unpack] using gap_stacks_disjoint R P (unpackGap s) (unpackGap t) hq

end DiamondIntegral.Section4.GammaBoundaryStackDisjointness
