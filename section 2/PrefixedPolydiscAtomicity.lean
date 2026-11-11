import «section 2».PrefixedDiscProducts
import «section 2».PrefixedCoordinateRelations
import «section 2».RectangleImages

/-! Lemma 2.25 with an existing finite tuple of ground disc names.
The varying-coordinate atomicity and Gamma base change remain the two
accepted unary inputs. The complete product argument is proved here. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped Classical

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem coordinate_update_with_disc_ground (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {G : Type} [LinearOrderedCommGroupWithZero G] (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (closed : Fin (n+1) → Bool) (a : Fin (n+1) → VF M) (δ : Fin (n+1) → Gamma M)
    (A : Set (Fin (n+1) → M)) (hA : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hsub : namedPolydisc closed a δ ⊆ A)
    (C : Set (Fin (n+1) → M))
    (hC : DefinableOverFiniteDiscNames B (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ) (fun _ => .vf) C)
    (b₀ : Fin (n+1) → M) (hb : b₀ ∈ namedPolydisc closed a δ) (hbC : b₀ ∈ C)
    (i : Fin (n+1)) (x : M) (hx : x ∈ BallImaginaries.underlying (finitePolydiscNames closed a δ i)) :
    Function.update b₀ i x ∈ C := by
  classical
  let b : Fin (n+1) → VF M := fun j => ⟨b₀ j,disc_underlying_subset_vf _ (hb j)⟩
  have hbval : vfValues b = b₀ := rfl
  have heNames : finitePolydiscNames closed b δ = finitePolydiscNames closed a δ :=
    finitePolydiscNames_recenter v hv closed a b δ (fun j => hb j)
  let E₀ := tupleBase B (Fin.removeNth i b₀)
  have hΓE : NontrivialDefinableGamma E₀ := hΓ.mono Set.subset_union_left (Set.Subset.refl _)
  let T : Set (Fin 1 → M) := {z | Fin.insertNth i (z 0) (Fin.removeNth i b₀) ∈ A}
  have hT : GeneratesTypeOverFiniteDiscNames E₀ ground d τ (fun _ => .vf) T :=
    hA.coordinate_fibre hc b₀ (hsub hb) i
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
  have hAtomic₀ := unary E₀ h00 hΓE k ground d τ T hT (closed i) (b i) (δ i) hUsub
  have hAtomic : IsAtomicOverFiniteDiscNames (coordinateDiscBase B b δ i)
      (Fin.snoc ground (closed i)) (Fin.snoc d (b i)) (Fin.snoc τ (δ i)) (fun _ : Fin 1 => .vf) U := by
    have h := lemma_2_23_disc_gamma_tuple h00 E₀ gamma hΓE _ _ _ _ U hAtomic₀ (Fin.removeNth i δ)
    simpa only [E₀,tupleBase,coordinateDiscBase,hbval] using h
  obtain ⟨R,hR⟩ := hC
  have heFull : finitePolydiscNames (Fin.append ground closed) (Fin.append d b) (Fin.append τ δ) =
      finitePolydiscNames (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ) := by
    rw [finitePolydiscNames_append,finitePolydiscNames_append,heNames]
  have hRb : R.fibre (Fin.append d b) (Fin.append τ δ) = C :=
    (R.fibre_eq_of_names _ _ _ _ heFull).trans hR
  let L : Set (Fin 1 → M) := {z | Function.update b₀ i (z 0) ∈ C}
  have hL : DefinableOverFiniteDiscNames (coordinateDiscBase B b δ i)
      (Fin.snoc ground (closed i)) (Fin.snoc d (b i)) (Fin.snoc τ (δ i)) (fun _ : Fin 1 => .vf) L := by
    refine ⟨R.prefixedCoordinateLine b δ i,?_⟩
    rw [R.prefixedCoordinateLine_fibre,hRb,hbval]
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

/-- The finite-radius 2.25 with every previously named ground disc retained.
The containing set need not be definable; zero source or ground arity is allowed. -/
theorem lemma_2_25_with_disc_ground (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    {k n : ℕ} (ground : Fin k → Bool) (d : Fin k → VF M) (τ : Fin k → Gamma M)
    (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (A : Set (Fin n → M)) (hA : GeneratesTypeOverFiniteDiscNames B ground d τ (fun _ => .vf) A)
    (hsub : namedPolydisc closed a δ ⊆ A) :
    IsAtomicOverFiniteDiscNames B (Fin.append ground closed) (Fin.append d a) (Fin.append τ δ)
      (fun _ => .vf) (namedPolydisc closed a δ) := by
  classical
  obtain ⟨G,hG,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hG
  refine ⟨namedPolydisc_definable_with_disc_ground h00 B (unary B) hΓ ground d τ closed a δ A hA hsub,
    namedPolydisc_nonempty closed a δ,namedPolydisc_proper closed a δ,?_⟩
  intro C hC
  have hstep (b : Fin n → M) (hb : b ∈ namedPolydisc closed a δ) (hbC : b ∈ C)
      (i : Fin n) (x : M) (hx : x ∈ BallImaginaries.underlying (finitePolydiscNames closed a δ i)) :
      Function.update b i x ∈ C := by
    cases n with
    | zero => exact i.elim0
    | succ n =>
      exact coordinate_update_with_disc_ground hc h00 B hΓ unary gamma v hv ground d τ
        closed a δ A hA hsub C hC b hb hbC i x hx
  by_cases hne : (namedPolydisc closed a δ ∩ C).Nonempty
  · obtain ⟨b,hb,hbC⟩ := hne
    left
    intro c hcD
    exact rectangle_induction (fun j => BallImaginaries.underlying (finitePolydiscNames closed a δ j))
      (fun z => z ∈ C) b hb hbC hstep c hcD
  · exact Or.inr (Set.disjoint_left.mpr (fun z hz hzC => hne ⟨z,hz,hzC⟩))

end DiamondIntegral.Section2
