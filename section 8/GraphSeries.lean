import «section 8».HmLattice
import FubiniTheorems.Prerequisites.Euler.GammaTupleMaps
import FubiniTheorems.Prerequisites.Euler.GammaBijectiveRelations
import FubiniTheorems.Prerequisites.Euler.GammaBoundedMapImage
import FubiniTheorems.Decomposition.GammaQEFiniteLaws

/-! The zeta series of the graph of a definable map, for Theorem 8.11.

Let `I ⊆ Γ^ℓ` be definable over the base and doubly bounded, and `E : Γ^ℓ → Γ^{k+1}` definable.
The series

  `∑_{m ≥ 1} ∑_{δ} A^{-m E₀(δ)} T^m`,

`δ` running over the points of `I` with `δ` and `E(δ)` in the lattice `π^{m⁻¹ℤ}`, is the
lattice-point series of the graph of `E` over `I` for the integral linear weight `−x₀`
(`graphSeries_eq`). By Lemma 8.9 it lies in `R[T]†` and has limit `−χ(graph E) = −χ(I)`
(`graph_hasLimit`).

In the proof of Theorem 8.11, `E(δ) = (w σ(δ), c)` with `σ` the weight of a sharp chart, `w` the
weight and `c` the value tuple of a piece of an RES chart: the integrality of the exponent and the
lattice condition on the RES piece become lattice conditions on the coordinates of the graph. -/

set_option autoImplicit false

noncomputable section

namespace DiamondIntegral.Section8.PuiseuxValues

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 GammaOrderLogic GammaDefinableMaps
open GammaBijectiveRelations FiniteTupleBlocks
open DiamondIntegral.Section8.GammaCells DiamondIntegral.Section5.PuiseuxOriginal

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

/-- The geometric Euler characteristic over the base of Section 8. -/
def chi {n : ℕ} (I : Set (Fin n → Γ)) (hI : GammaDefinable (base P) I) : ℤ :=
  GammaIteratedIntegral.integrateAll P.G.model00 P.G.uncountable.le P.G.saturated (base P)
    P.G.small_real (by simpa using Cardinal.aleph0_pos.trans P.G.uncountable) EulerKind.geometric n
    (GammaIndicators.indicatorFamily (base P) I hI)

/-- The exponent `m r(γ)` of a lattice point `γ`. -/
def latExp (m : ℕ) (γ : Γ) : ℤ := ⌊(m : ℚ) * ratValue π γ⌋

theorem latExp_qpow {m : ℕ} (hm : m ≠ 0) (z : ℤ) : latExp P m (qpow π ((z : ℚ) / m)) = z := by
  rw [latExp, ratValue_qpow (one_lt_uniformizerValue P)]
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [mul_div_cancel₀ _ hmq, Int.floor_intCast]

theorem qpow_div_injective {m : ℕ} (hm : m ≠ 0) {z z' : ℤ}
    (h : qpow π ((z : ℚ) / m) = qpow π ((z' : ℚ) / m)) : z = z' := by
  have := congrArg (latExp P m) h
  rwa [latExp_qpow P hm, latExp_qpow P hm] at this

/-- The lattice points of `I` at level `m` at which `E` also takes lattice values. -/
def latPts {ℓ k : ℕ} (m : ℕ) (I : Set (Fin ℓ → Γ)) (E : (Fin ℓ → Γ) → Fin k → Γ) : Set (Fin ℓ → Γ) :=
  {δ | δ ∈ I ∧ (∀ i, InLattice π m (δ i)) ∧ ∀ j, InLattice π m (E δ j)}

/-- The zeta series of the graph of `E` over `I`, weighted by the first coordinate of `E`. -/
def graphSeries {R : Type*} [CommRing R] (A : Rˣ) {ℓ k : ℕ} (I : Set (Fin ℓ → Γ))
    (E : (Fin ℓ → Γ) → Fin (k + 1) → Γ) : PowerSeries R :=
  PowerSeries.mk fun m => if m = 0 then 0 else
    ∑ᶠ δ ∈ latPts P m I E, ((A ^ (-latExp P m (E δ 0)) : Rˣ) : R)

theorem funext_blocks {α : Type*} {n m : ℕ} {f g : Fin (n + m) → α}
    (h1 : f ∘ headIndex n m = g ∘ headIndex n m) (h2 : f ∘ tailIndex n m = g ∘ tailIndex n m) :
    f = g := by
  rw [← join_reconstruct n m f, ← join_reconstruct n m g, h1, h2]

theorem comp_join {α β : Type*} {n m : ℕ} (φ : α → β) (u : Fin m → α) (y : Fin n → α) :
    φ ∘ join n m u y = join n m (φ ∘ u) (φ ∘ y) := by
  refine funext_blocks ?_ ?_
  · funext i
    simp [Function.comp]
  · funext i
    simp [Function.comp]

/-- The weight `−x₀` on the graph, in reversed coordinates. -/
def graphWt {ℓ k : ℕ} (x : Fin (k + 1 + ℓ) → ℤ) (_m : ℕ) : ℤ := -x (Fin.rev (tailIndex (k + 1) ℓ 0))

/-- **The graph series is a lattice-point series.** -/
theorem graphSeries_eq {R : Type*} [CommRing R] (A : Rˣ) {ℓ k : ℕ} (I : Set (Fin ℓ → Γ))
    (E : (Fin ℓ → Γ) → Fin (k + 1) → Γ) :
    graphSeries P A I E = SimplexSeries.latticeSeries A (ratTrace π (graphOn I E)) graphWt := by
  ext m
  simp only [graphSeries, SimplexSeries.latticeSeries, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · simp [hm]
  simp only [hm, ↓reduceIte]
  -- the point of `Γ^{k+1+ℓ}` of an integral point
  let y : (Fin (k + 1 + ℓ) → ℤ) → Fin (k + 1 + ℓ) → Γ :=
    fun x i => qpow π ((x (Fin.rev i) : ℚ) / m)
  let φ : (Fin (k + 1 + ℓ) → ℤ) → Fin ℓ → Γ := fun x => y x ∘ headIndex (k + 1) ℓ
  let S := {x : Fin (k + 1 + ℓ) → ℤ | (fun i => (x i : ℚ) / m) ∈ ratTrace π (graphOn I E)}
  have hmemS : ∀ x, x ∈ S ↔ y x ∈ graphOn I E := fun x => Iff.rfl
  have himg : latPts P m I E = φ '' S := by
    ext δ
    constructor
    · rintro ⟨hδ, hl, hE⟩
      choose z hz using fun i => eq_qpow_of_inLattice hm (hl i)
      choose z' hz' using fun j => eq_qpow_of_inLattice hm (hE j)
      let u : Fin (k + 1 + ℓ) → ℤ := join (k + 1) ℓ z z'
      have hy : y (u ∘ Fin.rev) = join (k + 1) ℓ δ (E δ) := by
        have h1 : y (u ∘ Fin.rev) = (fun t : ℤ => qpow π ((t : ℚ) / m)) ∘ u := by
          funext i
          simp [y, Fin.rev_rev]
        rw [h1, comp_join]
        congr 1
        · funext i; exact (hz i).symm
        · funext j; exact (hz' j).symm
      refine ⟨u ∘ Fin.rev, ?_, ?_⟩
      · rw [hmemS, hy]
        exact (graphOn_join I E δ (E δ)).mpr ⟨hδ, rfl⟩
      · change y (u ∘ Fin.rev) ∘ headIndex (k + 1) ℓ = δ
        rw [hy]
        funext i
        simp
    · rintro ⟨x, hx, rfl⟩
      rw [hmemS] at hx
      obtain ⟨hI, hE⟩ := hx
      refine ⟨hI, fun i => inLattice_qpow π _ hm, fun j => ?_⟩
      rw [hE]
      exact inLattice_qpow π _ hm
  have hinj : Set.InjOn φ S := by
    intro x hx x' hx' h
    rw [hmemS] at hx hx'
    have hyy : y x = y x' := by
      refine funext_blocks h ?_
      rw [← hx.2, ← hx'.2]
      exact congrArg E h
    funext i
    have := congrFun hyy (Fin.rev i)
    simp only [y, Fin.rev_rev] at this
    exact qpow_div_injective P hm this
  rw [himg, finsum_mem_image hinj]
  refine finsum_mem_congr rfl fun x hx => ?_
  rw [hmemS] at hx
  have hE0 : E (φ x) 0 = qpow π ((x (Fin.rev (tailIndex (k + 1) ℓ 0)) : ℚ) / m) := by
    have := congrFun hx.2 0
    simpa [φ, y] using this
  rw [hE0, latExp_qpow P hm]
  rfl

theorem graphOn_definable {ℓ k : ℕ} (I : Set (Fin ℓ → Γ)) (hI : GammaDefinable (base P) I)
    (E : (Fin ℓ → Γ) → Fin k → Γ) (hE : ∀ j, MapDefinable (base P) (fun δ => E δ j)) :
    GammaDefinable (base P) (graphOn I E) :=
  GammaTupleMaps.graph_definable (base P) I hI E hE

/-- `χ(graph E) = χ(I)`. -/
theorem chi_graphOn {ℓ k : ℕ} (I : Set (Fin ℓ → Γ)) (hI : GammaDefinable (base P) I)
    (E : (Fin ℓ → Γ) → Fin k → Γ) (hE : ∀ j, MapDefinable (base P) (fun δ => E δ j)) :
    chi P (graphOn I E) (graphOn_definable P I hI E hE) = chi P I hI := by
  refine integrateAll_bijOn P.G.model00 Section5.GammaQE.gamma_piecewise_rational_affine
    P.G.uncountable.le P.G.saturated (base P) P.G.small_real _ (Hm.base_nontrivial P)
    EulerKind.geometric ℓ (k + ℓ) _ _ I hI (fun z => z ∘ headIndex k ℓ)
    (GammaTupleMaps.graph_definable (base P) _ (graphOn_definable P I hI E hE) _
      fun i => projection_definable (base P) (headIndex k ℓ i)) ⟨fun z hz => hz.1, ?_, ?_⟩
  · intro z hz z' hz' h
    refine funext_blocks h ?_
    rw [← hz.2, ← hz'.2]
    exact congrArg E h
  · intro δ hδ
    refine ⟨join k ℓ δ (E δ), (graphOn_join I E δ (E δ)).mpr ⟨hδ, rfl⟩, ?_⟩
    funext i
    simp

/-- A bound for a finite family of bounds. -/
theorem exists_common_bound {ι : Type*} [Fintype ι] (β : ι → Γ) :
    ∃ b : Γ, 1 ≤ b ∧ ∀ i, β i ≤ b := by
  refine ⟨(insert 1 (Finset.univ.image β)).max' (Finset.insert_nonempty _ _),
    Finset.le_max' _ _ (Finset.mem_insert_self _ _), fun i => Finset.le_max' _ _ ?_⟩
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem β (Finset.mem_univ i))

theorem graphOn_bounded {ℓ k : ℕ} (I : Set (Fin ℓ → Γ)) (hI : GammaDefinable (base P) I) (β : Γ)
    (hβ : ∀ z ∈ I, ∀ i, β⁻¹ ≤ z i ∧ z i ≤ β)
    (E : (Fin ℓ → Γ) → Fin k → Γ) (hE : ∀ j, MapDefinable (base P) (fun δ => E δ j)) :
    ∃ N : ℕ, ∀ z ∈ graphOn I E, ∀ i, π ^ (-(N : ℤ)) ≤ z i ∧ z i ≤ π ^ (N : ℤ) := by
  have hb : ∀ j, ∃ γ : Γ, ∀ u ∈ I, γ⁻¹ ≤ E u j ∧ E u j ≤ γ := fun j =>
    GammaBoundedMapImage.bounded_map_image P.hc P.G.model00 Section5.GammaQE.gamma_piecewise_rational_affine
      P.G.uncountable.le P.G.saturated (base P) P.G.small_real
      (by simpa using Cardinal.aleph0_pos.trans P.G.uncountable) (Hm.base_nontrivial P) I hI
      (fun δ => E δ j) (hE j) ⟨β, hβ⟩
  choose γ hγ using hb
  obtain ⟨b, hb1, hbβ⟩ := exists_common_bound P (Option.elim · β γ)
  have key : ∀ (c x : Γ), c ≤ b → c⁻¹ ≤ x ∧ x ≤ c → b⁻¹ ≤ x ∧ x ≤ b :=
    fun c x hcb hx => ⟨(inv_le_inv_iff.mpr hcb).trans hx.1, hx.2.trans hcb⟩
  refine exists_pow_bound P _ (graphOn_definable P I hI E hE) b fun z hz i => ?_
  rw [← join_reconstruct k ℓ z] at hz ⊢
  obtain ⟨hzI, hzE⟩ := (graphOn_join I E _ _).mp hz
  have hcases : (∃ i', i = headIndex k ℓ i') ∨ ∃ j, i = tailIndex k ℓ j := by
    by_contra hne
    push Not at hne
    have h1 := congrFun (join_reconstruct k ℓ (fun t : Fin (k + ℓ) => decide (t = i))) i
    have hh : (fun t : Fin (k + ℓ) => decide (t = i)) ∘ headIndex k ℓ = fun _ => false := by
      funext i'; simp [Function.comp, (hne.1 i').symm]
    have ht : (fun t : Fin (k + ℓ) => decide (t = i)) ∘ tailIndex k ℓ = fun _ => false := by
      funext j; simp [Function.comp, (hne.2 j).symm]
    rw [hh, ht] at h1
    have h2 : join k ℓ (fun _ : Fin ℓ => false) (fun _ : Fin k => false) i = false := by
      have := congrFun (join_reconstruct k ℓ (fun _ : Fin (k + ℓ) => false)) i
      simpa [Function.comp] using this
    rw [h2] at h1
    simp at h1
  rcases hcases with ⟨i', rfl⟩ | ⟨j, rfl⟩
  · rw [join_head]
    exact key β _ (hbβ none) (hβ _ hzI i')
  · rw [join_tail, ← hzE]
    exact key (γ j) _ (hbβ (some j)) (hγ j _ hzI)

/-- **The zeta series of a graph.** -/
theorem graph_hasLimit {ℓ k : ℕ} (I : Set (Fin ℓ → Γ)) (hI : GammaDefinable (base P) I) (β : Γ)
    (hβ : ∀ z ∈ I, ∀ i, β⁻¹ ≤ z i ∧ z i ≤ β)
    (E : (Fin ℓ → Γ) → Fin (k + 1) → Γ) (hE : ∀ j, MapDefinable (base P) (fun δ => E δ j))
    {R : Type*} [CommRing R] (A : Rˣ) :
    RationalSeries.HasLimit A (graphSeries P A I E) (-(chi P I hI : R)) := by
  obtain ⟨N, hN⟩ := graphOn_bounded P I hI β hβ E hE
  have hX := graphOn_definable P I hI E hE
  have h := lemma_8_9 P (graphOn I E) hX N hN (ρ := Unit) (fun _ => graphOn I E) (fun _ => hX)
    (fun z hz => Set.mem_iUnion.mpr ⟨(), hz⟩)
    (fun _ i => if i = Fin.rev (tailIndex (k + 1) ℓ 0) then -1 else 0) (fun _ => 0) graphWt
    (fun _ x m _ => by simp [graphWt, ite_mul, Finset.sum_ite_eq']) A
  rw [graphSeries_eq]
  have hc := chi_graphOn P I hI E hE
  unfold chi at hc
  rw [hc] at h
  exact h

end DiamondIntegral.Section8.PuiseuxValues
