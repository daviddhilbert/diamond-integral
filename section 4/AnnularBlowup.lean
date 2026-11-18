import «section 4».RVDefinableGraphExtension
import «section 4».RVScaledRays

/-! Definition 7.2 (`defn:blowup:coa`), first layer.

The data of an elementary annular blowup with a bounded variable aperture:
the aperture function on the full retained RV domain with one named bound,
the inactive structural projection, the shell `0 < vrv s ≤ γ(u)` and the
separately tagged endpoint `s = τ(u)`, and the blown-up structural map
`f♭_j(u,s) = s · f_j(u)`. The main result here is that the finite-to-one
condition of Definition 7.2 makes the blown-up structural map finite-to-one
on both pieces. The packaging as a bounded chart comes in a later module.
Multiplicative Gamma: `1 ≤ codeValue τ` is the paper's `0 ≤ vrv τ`. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.AnnularBlowup
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Right cancellation of RV multiplication by a nonzero RV element. -/
theorem rvMul_right_cancel {s s' c : M} (hs : iRV s) (hs' : iRV s') (hc : NonzeroRV c)
    (h : iRVMul s c = iRVMul s' c) : s = s' := by
  have hr : (⟨s, hs⟩ : CanonicalRV.RVSort M) * ⟨c, hc.1⟩ =
      (⟨s', hs'⟩ : CanonicalRV.RVSort M) * ⟨c, hc.1⟩ := by
    apply Subtype.ext
    simpa only [RVOperations.mul_val] using h
  have hc0 : (⟨c, hc.1⟩ : CanonicalRV.RVSort M) ≠ 0 := by
    intro h0
    exact hc.2 ((congrArg Subtype.val h0).trans RVOperations.zero_val)
  exact congrArg Subtype.val (mul_right_cancel₀ hc0 hr)

variable {B : Base (M := M)} {k : ℕ}

/-- The inactive structural projection: coordinate `j` is replaced by `1`. -/
def inactive (r : Chart B k) (j : Fin k) (u : Fin r.arity → M) : Fin k → M :=
  Function.update (r.coordinate u) j iRVOne

/-- The finite-to-one condition of Definition 7.2 on `pr_{~j} ↾ f(U)`, stated
on the domain: `f` is finite-to-one, so this is equivalent to it. -/
def InactiveFinite (r : Chart B k) (j : Fin k) : Prop :=
  ∀ t : Fin k → M, {u | u ∈ r.domain ∧ inactive r j u = t}.Finite

/-- An aperture: an actual original-base definable RV function on the full
retained domain, nonzero, with `0 ≤ vrv τ ≤ Δ` for one named bound. Its
whole graph is retained, also when its image is infinite. -/
structure Aperture (r : Chart B k) where
  aperture : (Fin r.arity → M) → M
  graph_definable : DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv)
    (RVDefinableGraphExtension.domain r aperture)
  nonzero : ∀ u ∈ r.domain, NonzeroRV (aperture u)
  nonnegative : ∀ u ∈ r.domain, 1 ≤ codeValue (aperture u)
  bound : Values.Gamma (M := M)
  bounded : ∀ u ∈ r.domain, codeValue (aperture u) ≤ bound

/-- The blown-up structural map `f♭(u,s)`: `s · f_j(u)` in position `j`. -/
def blownCoordinate (r : Chart B k) (j : Fin k) (u : Fin r.arity → M) (s : M) :
    Fin k → M :=
  Function.update (r.coordinate u) j (iRVMul s (r.coordinate u j))

/-- The shell `{(u,s) : 0 < vrv s ≤ γ(u)}`. -/
def shellPoints (r : Chart B k) (τ : Aperture r) : Set ((Fin r.arity → M) × M) :=
  {p | p.1 ∈ r.domain ∧ NonzeroRV p.2 ∧ 1 < codeValue p.2 ∧
    codeValue p.2 ≤ codeValue (τ.aperture p.1)}

/-- The separately tagged endpoint graph `{(u, τ(u))}`. -/
def endpointPoints (r : Chart B k) (τ : Aperture r) : Set ((Fin r.arity → M) × M) :=
  {p | p.1 ∈ r.domain ∧ p.2 = τ.aperture p.1}

theorem inactive_blownCoordinate (r : Chart B k) (j : Fin k) (u : Fin r.arity → M) (s : M) :
    Function.update (blownCoordinate r j u s) j iRVOne = inactive r j u := by
  simp only [blownCoordinate, inactive, Function.update_idem]

theorem blownCoordinate_at (r : Chart B k) (j : Fin k) (u : Fin r.arity → M) (s : M) :
    blownCoordinate r j u s j = iRVMul s (r.coordinate u j) := by
  simp only [blownCoordinate, Function.update_self]

/-- A fibre of `f♭` projects into a fibre of the inactive projection. -/
theorem fst_mem_inactive_fibre (r : Chart B k) (j : Fin k) {t : Fin k → M}
    {p : (Fin r.arity → M) × M} (hp : p.1 ∈ r.domain) (he : blownCoordinate r j p.1 p.2 = t) :
    p.1 ∈ {u | u ∈ r.domain ∧ inactive r j u = Function.update t j iRVOne} := by
  refine ⟨hp, ?_⟩
  rw [← he, inactive_blownCoordinate]

/-- Definition 7.2: on the shell, the blown-up structural map is finite-to-one. -/
theorem shell_finite_fibres (r : Chart B k) (j : Fin k) (hfin : InactiveFinite r j)
    (τ : Aperture r) (t : Fin k → M) :
    {p | p ∈ shellPoints r τ ∧ blownCoordinate r j p.1 p.2 = t}.Finite := by
  refine Set.Finite.of_finite_image (f := Prod.fst) ?_ ?_
  · apply (hfin (Function.update t j iRVOne)).subset
    rintro u ⟨p, ⟨hp, he⟩, rfl⟩
    exact fst_mem_inactive_fibre r j hp.1 he
  · rintro p ⟨hp, he⟩ q ⟨hq, hf⟩ h1
    have hc : NonzeroRV (r.coordinate p.1 j) := r.coordinate_proper p.1 hp.1 j
    have hpj := blownCoordinate_at r j p.1 p.2
    have hqj := blownCoordinate_at r j q.1 q.2
    rw [he] at hpj
    rw [hf, ← h1] at hqj
    have h2 : p.2 = q.2 := rvMul_right_cancel hp.2.1.1 hq.2.1.1 hc (hpj.symm.trans hqj)
    exact Prod.ext h1 h2

/-- Definition 7.2: on the endpoint graph, the blown-up structural map is finite-to-one. -/
theorem endpoint_finite_fibres (r : Chart B k) (j : Fin k) (hfin : InactiveFinite r j)
    (τ : Aperture r) (t : Fin k → M) :
    {p | p ∈ endpointPoints r τ ∧ blownCoordinate r j p.1 p.2 = t}.Finite := by
  refine Set.Finite.of_finite_image (f := Prod.fst) ?_ ?_
  · apply (hfin (Function.update t j iRVOne)).subset
    rintro u ⟨p, ⟨hp, he⟩, rfl⟩
    exact fst_mem_inactive_fibre r j hp.1 he
  · rintro p ⟨hp, _⟩ q ⟨hq, _⟩ h1
    exact Prod.ext h1 (by rw [hp.2, hq.2, h1])

/-- Remark 7.4: the new coordinate on the shell lies in `(1, Δ]`, so it is
doubly bounded with the named bound of the aperture. -/
theorem shell_coordinate_bounded (r : Chart B k) (τ : Aperture r)
    {p : (Fin r.arity → M) × M} (hp : p ∈ shellPoints r τ) :
    1 < codeValue p.2 ∧ codeValue p.2 ≤ τ.bound :=
  ⟨hp.2.2.1, hp.2.2.2.trans (τ.bounded p.1 hp.1)⟩

/-- Remark 7.4 for the endpoint coordinate. -/
theorem endpoint_coordinate_bounded (r : Chart B k) (τ : Aperture r)
    {p : (Fin r.arity → M) × M} (hp : p ∈ endpointPoints r τ) :
    1 ≤ codeValue p.2 ∧ codeValue p.2 ≤ τ.bound := by
  rw [hp.2]
  exact ⟨τ.nonnegative p.1 hp.1, τ.bounded p.1 hp.1⟩

end DiamondIntegral.Section4.AnnularBlowup
