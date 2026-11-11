import «section 2».DiscNameProducts
import «section 2».CoordinateDiscNames

/-!
# Lemma 2.25 for finite-radius polydiscs

The unary theorem and Gamma base change are explicit accepted inputs from
[18, Section 3]. The product argument is proved here: make each coordinate
disc atomic over its own name, then adjoin the other radii and use coordinate
chains. The varying coordinate is never named as a ground VF point.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem coordinate_update_named_disc (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {G : Type} [LinearOrderedCommGroupWithZero G] (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    {n : ℕ} (closed : Fin (n+1) → Bool) (a : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M)
    (A : Set (Fin (n+1) → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : namedPolydisc closed a δ ⊆ A)
    (C : Set (Fin (n+1) → M)) (hC : DefinableOverFiniteDiscNames B closed a δ (fun _ => .vf) C)
    (b₀ : Fin (n+1) → M) (hb : b₀ ∈ namedPolydisc closed a δ) (hbC : b₀ ∈ C)
    (i : Fin (n+1)) (x : M)
    (hx : x ∈ BallImaginaries.underlying (finitePolydiscNames closed a δ i)) :
    Function.update b₀ i x ∈ C := by
  classical
  let b : Fin (n+1) → VF M := fun j => ⟨b₀ j, disc_underlying_subset_vf _ (hb j)⟩
  have hbval : SpecialTransformations.Section4.vfValues b = b₀ := rfl
  have heNames : finitePolydiscNames closed b δ = finitePolydiscNames closed a δ :=
    finitePolydiscNames_recenter v hv closed a b δ (fun j => hb j)
  let E₀ := tupleBase B (Fin.removeNth i b₀)
  have hΓE : NontrivialDefinableGamma E₀ :=
    hΓ.mono Set.subset_union_left (Set.Subset.refl _)
  let T : Set (Fin 1 → M) := {z | Fin.insertNth i (z 0) (Fin.removeNth i b₀) ∈ A}
  have hT : GeneratesCompleteType E₀ (fun _ => .vf) T := hA.coordinate_fibre b₀ (hsub hb) i
  let U : Set (Fin 1 → M) := {z | z 0 ∈ BallImaginaries.underlying
    (if closed i then closedDiscCode (b i) (δ i).val else openDiscCode (b i) (δ i))}
  have heDi : (if closed i then closedDiscCode (b i) (δ i).val else openDiscCode (b i) (δ i)) =
      finitePolydiscNames closed a δ i := congrFun heNames i
  have hUsub : U ⊆ T := by
    intro z hz
    change z 0 ∈ BallImaginaries.underlying _ at hz
    rw [heDi] at hz
    have hw : Function.update b₀ i (z 0) ∈ namedPolydisc closed a δ := by
      intro j
      by_cases hj : j = i
      · subst j
        simpa only [Function.update_self] using hz
      · simpa only [Function.update_of_ne hj] using hb j
    change Fin.insertNth i (z 0) (Fin.removeNth i b₀) ∈ A
    simpa only [Fin.insertNth_removeNth] using hsub hw
  have hAtomic₀ := lemma_2_25_unary h00 E₀ (unary E₀) hΓE T hT (closed i) (b i) (δ i) hUsub
  have hAtomic : IsAtomicOverFiniteDiscNames (coordinateDiscBase B b δ i)
      (![closed i]) (![b i]) (![δ i]) (fun _ : Fin 1 => .vf) U := by
    have h := lemma_2_23_disc_gamma_tuple h00 E₀ gamma hΓE (![closed i]) (![b i]) (![δ i])
      (fun _ : Fin 1 => .vf) U hAtomic₀ (Fin.removeNth i δ)
    simpa only [E₀, tupleBase, coordinateDiscBase, hbval] using h
  obtain ⟨R, hR⟩ := hC
  have hRb : R.fibre b δ = C := (R.fibre_eq_of_names b a δ δ heNames).trans hR
  let L : Set (Fin 1 → M) := {z | Function.update b₀ i (z 0) ∈ C}
  have hL : DefinableOverFiniteDiscNames (coordinateDiscBase B b δ i)
      (![closed i]) (![b i]) (![δ i]) (fun _ : Fin 1 => .vf) L := by
    refine ⟨R.coordinateLine b δ i, ?_⟩
    rw [R.coordinateLine_fibre, hRb, hbval]
  have hxU : (fun _ : Fin 1 => x) ∈ U := by
    change x ∈ BallImaginaries.underlying _
    rwa [heDi]
  rcases hAtomic.2.2.2 L hL with hUL | hdis
  · exact hUL hxU
  · have hbU : (fun _ : Fin 1 => b₀ i) ∈ U := by
      change b₀ i ∈ BallImaginaries.underlying _
      rw [heDi]
      exact hb i
    have hbL : (fun _ : Fin 1 => b₀ i) ∈ L := by
      change Function.update b₀ i (b₀ i) ∈ C
      simpa only [Function.update_eq_self] using hbC
    exact (Set.disjoint_left.mp hdis hbU hbL).elim

/-- Lemma 2.25 in all finite open/closed radius charts, relative only to
the accepted unary and Gamma results of [18]. The set A need not be
definable. All actual disc names, and the original base, are retained.
Zero coordinates and mixed open/closed products are included. -/
theorem lemma_2_25_finite_names (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {n : ℕ} (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (A : Set (Fin n → M)) (hA : GeneratesCompleteType B (fun _ => .vf) A)
    (hsub : namedPolydisc closed a δ ⊆ A) :
    IsAtomicOverFiniteDiscNames B closed a δ (fun _ => .vf) (namedPolydisc closed a δ) := by
  classical
  obtain ⟨G, hG, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hG
  refine ⟨namedPolydisc_definable_of_type h00 B (unary B) hΓ closed a δ A hA hsub,
    namedPolydisc_nonempty closed a δ, namedPolydisc_proper closed a δ, ?_⟩
  intro C hC
  have hstep (b : Fin n → M) (hb : b ∈ namedPolydisc closed a δ) (hbC : b ∈ C)
      (i : Fin n) (x : M)
      (hx : x ∈ BallImaginaries.underlying (finitePolydiscNames closed a δ i)) :
      Function.update b i x ∈ C := by
    cases n with
    | zero => exact i.elim0
    | succ k =>
      exact coordinate_update_named_disc h00 B hΓ unary gamma v hv closed a δ A hA hsub C hC
        b hb hbC i x hx
  by_cases hne : (namedPolydisc closed a δ ∩ C).Nonempty
  · obtain ⟨b, hb, hbC⟩ := hne
    left
    intro c hc
    let w (s : Finset (Fin n)) : Fin n → M := fun j => if j ∈ s then c j else b j
    have hwD (s : Finset (Fin n)) : w s ∈ namedPolydisc closed a δ := by
      intro j
      by_cases hj : j ∈ s
      · simpa only [w, ite_eq_left hj] using hc j
      · simpa only [w, ite_eq_right hj] using hb j
    have hwC (s : Finset (Fin n)) : w s ∈ C := by
      induction s using Finset.induction_on with
      | empty => simpa only [w, Finset.notMem_empty, ite_false] using hbC
      | @insert i s _hi ih =>
        have h := hstep (w s) (hwD s) ih i (c i) (hc i)
        have he : w (insert i s) = Function.update (w s) i (c i) := by
          funext j
          by_cases hj : j = i
          · subst j
            simp [w]
          · simp [w, hj]
        rwa [he]
    simpa only [w, Finset.mem_univ, ite_true] using hwC Finset.univ
  · right
    exact Set.disjoint_left.mpr (fun z hz hzC => hne ⟨z, hz, hzC⟩)

end DiamondIntegral.Section2
