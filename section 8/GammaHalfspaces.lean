import «section 8».GammaCells
import «section 2».GammaStableEmbedding

/-! Definable subsets of `Γⁿ` as realizations of unions of sign classes.

`saturated_of_halfspaceBoolean`: a Boolean combination of half-spaces `{z : ∏ zᵢ^{mᵢ} ≤ δ}` whose
constants are rational powers of `π` is the realization `real S` of a union `S` of sign classes of
finitely many rational affine functions in `(Hull Γ)ⁿ`.

`codeSet_definable`: over a base without imaginary names, `GammaDefinable` gives the definability
hypothesis of `gamma_stably_embedded` (canonical structure).

`euler_eq_eulerChar`: in a saturated strongly homogeneous model with canonical structure, let `X` be
a subset of `Γⁿ` definable over a small base `⟨R, ∅⟩` whose substructure values are rational powers
of a definable `π > 1`. If `X` is doubly bounded by powers of `π`, the geometric Euler
characteristic of `X` is `Triangulation.eulerChar` of a triangulation of its rational trace
`{x ∈ ℚⁿ | (qpow π (x (rev i)))ᵢ ∈ X}`, which is a bounded union of sign classes. -/

set_option autoImplicit false

noncomputable section

namespace DiamondIntegral.Section8.GammaCells

open Prism
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 GammaOrderLogic
open DiamondIntegral.Section2.GammaStable

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

local notation "Γ" => Values.Gamma (M := M)

theorem SaturatedV.mono {n : ℕ} {e : Hull Γ} {G G' : List (AffFun n)} {S : Set (Fin n → Hull Γ)}
    (hS : SaturatedV e G S) (h : ∀ g ∈ G, g ∈ G') : SaturatedV e G' S :=
  fun z w hzw => hS z w fun g hg => hzw g (h g hg)

/-- The affine function `∑ m (rev j) yⱼ − q` of a half-space. -/
def halfspaceFun {n : ℕ} (m : Fin n → ℤ) (q : ℚ) : AffFun n := ⟨fun j => (m (Fin.rev j) : ℚ), -q⟩

theorem evalV_halfspaceFun {n : ℕ} (π : Γ) (m : Fin n → ℤ) (q : ℚ) (z : Fin n → Γ) :
    (halfspaceFun m q).evalV (ι π) (fun j => ι (z (Fin.rev j))) = ι (∏ i, z i ^ m i) - ι (qpow π q) := by
  rw [ι_prod, ι_qpow]
  simp only [AffFun.evalV, halfspaceFun, ι_zpow, neg_smul, ← sub_eq_add_neg]
  congr 1
  refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
  simp [Int.cast_smul_eq_zsmul]

/-- **Half-spaces with rational constants.** A Boolean combination of half-spaces whose
constants are rational powers of `π` is the realization of a union of sign classes. -/
theorem saturated_of_halfspaceBoolean {π : Γ} {Δ : Set Γ} (hΔ : ∀ δ ∈ Δ, ∃ q : ℚ, δ = qpow π q)
    {n : ℕ} {X : Set (Fin n → Γ)} (hX : HalfspaceBoolean Δ X) :
    ∃ (G : List (AffFun n)) (S : Set (Fin n → Hull Γ)), SaturatedV (ι π) G S ∧ X = real S := by
  induction hX with
  | halfspace m δ hδ =>
    obtain ⟨q, rfl⟩ := hΔ δ hδ
    refine ⟨[halfspaceFun m q], {w | (halfspaceFun m q).evalV (ι π) w ≤ 0}, ?_, ?_⟩
    · intro z w hzw
      have h := hzw _ List.mem_cons_self
      change (halfspaceFun m q).evalV (ι π) z ≤ 0 ↔ (halfspaceFun m q).evalV (ι π) w ≤ 0
      rw [← not_lt, ← not_lt, ← sign_eq_one_iff, ← sign_eq_one_iff, h]
    · ext z
      change ∏ i, z i ^ m i ≤ qpow π q ↔
        (halfspaceFun m q).evalV (ι π) (fun j => ι (z (Fin.rev j))) ≤ 0
      rw [evalV_halfspaceFun, sub_nonpos, ι_le_iff]
  | compl _ ih =>
    obtain ⟨G, S, hS, rfl⟩ := ih
    exact ⟨G, Sᶜ, fun z w hzw => not_congr (hS z w hzw), rfl⟩
  | inter _ _ ih ih' =>
    obtain ⟨G, S, hS, rfl⟩ := ih
    obtain ⟨G', S', hS', rfl⟩ := ih'
    refine ⟨G ++ G', S ∩ S', fun z w hzw => and_congr
      (SaturatedV.mono hS (fun g hg => List.mem_append_left _ hg) z w hzw)
      (SaturatedV.mono hS' (fun g hg => List.mem_append_right _ hg) z w hzw), rfl⟩
  | univ => exact ⟨[], Set.univ, fun _ _ _ => Iff.rfl, rfl⟩

/-- Over a base without imaginary names, `GammaDefinable` gives the definability of the code
set (canonical structure). -/
theorem codeSet_definable (hc : CanonicalStructure.IsCanonical (M := M)) (R : Set M) {n : ℕ}
    {X : Set (Fin n → Γ)} (hX : GammaDefinable ⟨R, ∅⟩ X) : R.Definable LRV (codeSet X) := by
  obtain ⟨k, γ, hγ, hA⟩ := hX
  cases k with
  | succ k => exact absurd (hγ 0) (Set.notMem_empty _)
  | zero =>
    have hA' := (GammaParameters.with_zero_iff R γ _ _).mp hA
    have hraw := ((definableOver_iff_normalized_raw R _ _).mp hA').1
    rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc] at hraw
    exact hraw

/-- The rational trace of a subset of `Γⁿ`, coordinates reversed. -/
def ratTrace (π : Γ) {n : ℕ} (X : Set (Fin n → Γ)) : Set (Fin n → ℚ) :=
  {x | (fun i => qpow π (x (Fin.rev i))) ∈ X}

theorem ratTrace_real (π : Γ) {n : ℕ} (S : Set (Fin n → Hull Γ)) :
    ratTrace π (real S) = {x | (fun i => x i • ι π) ∈ S} := by
  ext x
  simp [ratTrace, real, ι_qpow]

/-- **Euler characteristic of a definable bounded set.** -/
theorem euler_eq_eulerChar (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) (R : Set M) (hr : Cardinal.mk R < κ)
    {π : Γ} (hπ1 : 1 < π) (hπ : GammaDefinableClosureAtBase ⟨R, ∅⟩ π)
    (hΔ : ∀ δ ∈ substructureValues (Substructure.closure LRV R), ∃ q : ℚ, δ = qpow π q)
    {n : ℕ} (X : Set (Fin n → Γ)) (hX : GammaDefinable ⟨R, ∅⟩ X) (N : ℕ)
    (hbd : ∀ z ∈ X, ∀ i, π ^ (-(N : ℤ)) ≤ z i ∧ z i ≤ π ^ (N : ℤ)) :
    ∃ G : List (AffFun n), Constructible G (ratTrace π X) ∧ ratTrace π X ⊆ box n N ∧
      ∃ T : Triangulation n (ratTrace π X),
        GammaIteratedIntegral.integrateAll h00 hκ.le hs ⟨R, ∅⟩ hr (by simpa using Cardinal.aleph0_pos.trans hκ) EulerKind.geometric n
          (GammaIndicators.indicatorFamily ⟨R, ∅⟩ X hX) = T.eulerChar := by
  obtain ⟨G, S, hS, rfl⟩ := saturated_of_halfspaceBoolean hΔ
    (gamma_stably_embedded hc hκ hs hh R hr X (codeSet_definable hc R hX))
  have hbox : ∀ x : Fin n → ℚ, (fun i => x i • ι π) ∈ S → x ∈ box n N := by
    intro x hx i
    have hxX : (fun i => qpow π (x (Fin.rev i))) ∈ real S := by
      change (fun j => ι (qpow π (x (Fin.rev (Fin.rev j))))) ∈ S
      simpa only [ι_qpow, Fin.rev_rev] using hx
    obtain ⟨h1, h2⟩ := hbd _ hxX (Fin.rev i)
    simp only [Fin.rev_rev] at h1 h2
    have he := pos_ι_of_one_lt hπ1
    have h1' := ι_le_iff.mpr h1
    have h2' := ι_le_iff.mpr h2
    rw [ι_zpow_rat, ι_qpow] at h1'
    rw [ι_zpow_rat, ι_qpow] at h2'
    have h1'' := (smul_le_smul_iff_of_pos_right he).mp h1'
    have h2'' := (smul_le_smul_iff_of_pos_right he).mp h2'
    push_cast at h1'' h2''
    exact abs_le.mpr ⟨h1'', h2''⟩
  obtain ⟨hD, T, hT⟩ := euler_real h00 hκ.le hs ⟨R, ∅⟩ hr
    (by simpa using Cardinal.aleph0_pos.trans hκ) hπ1 hπ G S hS
    (Nat.cast_nonneg N) hbox hX
  rw [ratTrace_real]
  exact ⟨G, hD, hbox, T, hT⟩

theorem constructible_mono {n : ℕ} {G G' : List (AffFun n)} {D : Set (Fin n → ℚ)}
    (hD : Constructible G D) (h : ∀ g ∈ G, g ∈ G') : Constructible G' D :=
  fun x y hxy => hD x y fun g hg => hxy g (h g hg)

/-- The rational trace of a definable subset of `Γⁿ` is a union of sign classes. -/
theorem constructible_ratTrace (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) (R : Set M) (hr : Cardinal.mk R < κ)
    {π : Γ} (hπ1 : 1 < π)
    (hΔ : ∀ δ ∈ substructureValues (Substructure.closure LRV R), ∃ q : ℚ, δ = qpow π q)
    {n : ℕ} (X : Set (Fin n → Γ)) (hX : GammaDefinable ⟨R, ∅⟩ X) :
    ∃ G : List (AffFun n), Constructible G (ratTrace π X) := by
  obtain ⟨G, S, hS, rfl⟩ := saturated_of_halfspaceBoolean hΔ
    (gamma_stably_embedded hc hκ hs hh R hr X (codeSet_definable hc R hX))
  refine ⟨G, ?_⟩
  rw [ratTrace_real]
  exact (realV_of_saturated (pos_ι_of_one_lt hπ1) hS).1

/-- **Lemma 8.9 over the value group.** Let `X ⊆ Γⁿ` be definable over `⟨R, ∅⟩` and doubly bounded
by powers of `π`, covered by finitely many definable pieces `P r` on whose rational traces the
weight is integral affine in `(x, m)`. Then the lattice-point series of the rational trace of `X`
lies in `R'[T]†`, has degree `≤ 0`, and its limit is minus the geometric Euler characteristic of
`X`. -/
theorem hasLimit_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) (R : Set M) (hr : Cardinal.mk R < κ)
    {π : Γ} (hπ1 : 1 < π) (hπ : GammaDefinableClosureAtBase ⟨R, ∅⟩ π)
    (hΔ : ∀ δ ∈ substructureValues (Substructure.closure LRV R), ∃ q : ℚ, δ = qpow π q)
    {n : ℕ} (X : Set (Fin n → Γ)) (hX : GammaDefinable ⟨R, ∅⟩ X) (N : ℕ)
    (hbd : ∀ z ∈ X, ∀ i, π ^ (-(N : ℤ)) ≤ z i ∧ z i ≤ π ^ (N : ℤ))
    {ρ : Type} [Fintype ρ] (P : ρ → Set (Fin n → Γ)) (hP : ∀ r, GammaDefinable ⟨R, ∅⟩ (P r))
    (hcov : X ⊆ ⋃ r, P r) (a : ρ → Fin n → ℤ) (b : ρ → ℤ) (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (r : ρ) (x : Fin n → ℤ) (m : ℕ),
      (fun i => (x i : ℚ) / m) ∈ ratTrace π X ∩ ratTrace π (P r) →
        wt x m = ∑ i, a r i * x i + b r * m)
    {R' : Type*} [CommRing R'] (A : R'ˣ) :
    RationalSeries.HasLimit A (SimplexSeries.latticeSeries A (ratTrace π X) wt)
      (-((GammaIteratedIntegral.integrateAll h00 hκ.le hs ⟨R, ∅⟩ hr
        (by simpa using Cardinal.aleph0_pos.trans hκ) EulerKind.geometric n
          (GammaIndicators.indicatorFamily ⟨R, ∅⟩ X hX) : ℤ) : R')) := by
  classical
  obtain ⟨G₀, hD, hsub, T, hT⟩ := euler_eq_eulerChar hc h00 hκ hs hh R hr hπ1 hπ hΔ X hX N hbd
  choose GP hGP using fun r => constructible_ratTrace hc hκ hs hh R hr hπ1 hΔ (P r) (hP r)
  let G : List (AffFun n) := G₀ ++ (Finset.univ.toList : List ρ).flatMap GP
  have hG₀ : ∀ g ∈ G₀, g ∈ G := fun g hg => List.mem_append_left _ hg
  have hGr : ∀ r, ∀ g ∈ GP r, g ∈ G := fun r g hg => List.mem_append_right _
    (List.mem_flatMap.mpr ⟨r, Finset.mem_toList.mpr (Finset.mem_univ r), hg⟩)
  have hcovQ : ratTrace π X ⊆ ⋃ r, ratTrace π (P r) := fun x hx => by
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨r, hr⟩
  rw [hT]
  exact hasLimit_latticeSeries A G (Nat.cast_nonneg N) hsub (constructible_mono hD hG₀)
    (fun r => ratTrace π (P r)) (fun r => constructible_mono (hGP r) (hGr r)) hcovQ a b wt hwt T

end DiamondIntegral.Section8.GammaCells
