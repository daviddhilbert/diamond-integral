import «section 8».PuiseuxUniformizer

/-! Lemma 8.9 for weights with rational coefficients.

In Lemma 8.9 the weight is `wt x m = a · x + b m` on each piece, with `a`, `b` integral. In the
proof of Theorem 8.11 the weight is the value of a definable `RV`-valued function, which is
piecewise affine with rational coefficients and takes integral values at the lattice points; on a
piece of lower dimension the coefficients need not be integral. The proof of Step 3 only uses
that the weight is linear on the cone and integral at its lattice points: it is then integral on
the lattice points of the span of the cone, in particular on the integral generators of its rays.

* `hasLimit_openSimplex_rat`: Step 3 with `a`, `b` rational, using the subgroup of the lattice on
  which the rational weight is integral;
* `Prism.hasLimit_latticeSeries_rat`, `GammaCells.hasLimit_gamma_rat`,
  `PuiseuxValues.lemma_8_9_rat`: the rest of the proof of Lemma 8.9, unchanged. -/

set_option autoImplicit false

namespace DiamondIntegral.Section8.SimplexSeries

open RationalSeries LatticeCone

variable {R : Type*} [CommRing R] (A : Rˣ) {n : ℕ}

/-- The rational linear weight `(x, m) ↦ ∑ a_i x_i + b m`. -/
def ratWeight (a : Fin n → ℚ) (b : ℚ) : Lattice n →+ ℚ :=
  AddMonoidHom.mk' (fun x => ∑ i, a i * (x.1 i : ℚ) + b * (x.2 : ℚ)) (by
    intro x y
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
    ring)

theorem ratWeight_apply (a : Fin n → ℚ) (b : ℚ) (x : Lattice n) :
    ratWeight a b x = ∑ i, a i * (x.1 i : ℚ) + b * (x.2 : ℚ) := rfl

/-- The lattice points at which the rational weight is integral. -/
def intPts (a : Fin n → ℚ) (b : ℚ) : AddSubgroup (Lattice n) where
  carrier := {x | ∃ z : ℤ, ratWeight a b x = z}
  add_mem' := by
    rintro x y ⟨z, hz⟩ ⟨z', hz'⟩
    exact ⟨z + z', by rw [map_add, hz, hz', Int.cast_add]⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro x ⟨z, hz⟩
    exact ⟨-z, by rw [map_neg, hz, Int.cast_neg]⟩

theorem mem_intPts (a : Fin n → ℚ) (b : ℚ) (x : Lattice n) :
    x ∈ intPts a b ↔ ∃ z : ℤ, ratWeight a b x = z := Iff.rfl

/-- The weight on `intPts`, as an integral additive map. -/
noncomputable def intWeight (a : Fin n → ℚ) (b : ℚ) : intPts a b →+ ℤ :=
  AddMonoidHom.mk' (fun x => ((mem_intPts a b x).mp x.2).choose) (by
    intro x y
    have h := ((mem_intPts a b _).mp (x + y).2).choose_spec
    have hx := ((mem_intPts a b _).mp x.2).choose_spec
    have hy := ((mem_intPts a b _).mp y.2).choose_spec
    have : ((((mem_intPts a b _).mp (x + y).2).choose : ℤ) : ℚ) =
        (((mem_intPts a b _).mp x.2).choose : ℚ) + ((mem_intPts a b _).mp y.2).choose := by
      rw [← h, ← hx, ← hy, AddSubgroup.coe_add, map_add]
    exact_mod_cast this)

theorem intWeight_spec (a : Fin n → ℚ) (b : ℚ) (x : intPts a b) :
    (intWeight a b x : ℚ) = ratWeight a b x :=
  ((mem_intPts a b _).mp x.2).choose_spec.symm

section cone

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {g : ι → Fin n → ℤ} {d : ι → ℕ}

/-- A point of the cone: the rational weight is integral there and equals `wt`. -/
theorem cone_int [Nonempty ι] {w : ι → Fin n → ℚ} (hd : ∀ j, 0 < d j)
    (hg : ∀ j i, (g j i : ℚ) = d j * w j i) (a : Fin n → ℚ) (b : ℚ) (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (x : Fin n → ℤ) (m : ℕ), (fun i => (x i : ℚ) / m) ∈ openSimplex w →
      (wt x m : ℚ) = ∑ i, a i * x i + b * m)
    {x : Lattice n} (hx : x ∈ coneSet (parallelepipedFinset g d) (gen g d) Finset.univ) :
    x ∈ intPts a b ∧ 0 < x.2 ∧ ratWeight a b x = wt x.1 x.2.toNat := by
  obtain ⟨c, hr, hc⟩ := (mem_coneSet_iff x).mp hx
  have hpos : (0 : ℚ) < x.2 := by
    rw [hr.1]
    exact Finset.sum_pos (fun j _ => mul_pos (hc j) (Nat.cast_pos.mpr (hd j))) Finset.univ_nonempty
  have hpos' : 0 < x.2 := by exact_mod_cast hpos
  have hm : x.2.toNat ≠ 0 := by omega
  have hxe : ((x.1, ((x.2.toNat : ℕ) : ℤ)) : Lattice n) = x :=
    Prod.ext rfl (Int.toNat_of_nonneg hpos'.le)
  have hs : (fun i => (x.1 i : ℚ) / x.2.toNat) ∈ openSimplex w :=
    (cone_iff_simplex hd hg x.1 hm).mp (by rw [hxe]; exact ⟨c, hr, hc⟩)
  have he : ratWeight a b x = wt x.1 x.2.toNat := by
    rw [hwt _ _ hs, ratWeight_apply]
    congr 2
    exact_mod_cast (Int.toNat_of_nonneg hpos'.le).symm
  exact ⟨⟨_, he⟩, hpos', he⟩

/-- **Step 3 with rational coefficients.** -/
theorem hasLimit_openSimplex_of_generators_rat [Nonempty ι] {w : ι → Fin n → ℚ}
    (hw : AffineIndependent ℚ w) (hd : ∀ j, 0 < d j) (hg : ∀ j i, (g j i : ℚ) = d j * w j i)
    (a : Fin n → ℚ) (b : ℚ) (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (x : Fin n → ℤ) (m : ℕ), (fun i => (x i : ℚ) / m) ∈ openSimplex w →
      (wt x m : ℚ) = ∑ i, a i * x i + b * m) :
    HasLimit A (latticeSeries A (openSimplex w) wt) ((-1) ^ Fintype.card ι) := by
  classical
  have hLI := independent_of_affineIndependent hw hd hg
  have hcone := fun (x : Lattice n) (hx : x ∈ coneSet (parallelepipedFinset g d) (gen g d) Finset.univ) =>
    cone_int hd hg a b wt hwt hx
  have hPc : ∀ p ∈ parallelepipedFinset g d,
      p ∈ coneSet (parallelepipedFinset g d) (gen g d) Finset.univ :=
    fun p hp => ⟨p, hp, 0, fun _ _ => rfl, by simp⟩
  have hPH : ∀ p ∈ parallelepipedFinset g d, p ∈ intPts a b := fun p hp => (hcone p (hPc p hp)).1
  have hgenH : ∀ j, gen g d j ∈ intPts a b := by
    intro j
    have h1 : ∑ i, gen g d i + gen g d j ∈ coneSet (parallelepipedFinset g d) (gen g d) Finset.univ :=
      ⟨_, sum_gen_mem, Pi.single j 1, fun _ h => absurd (Finset.mem_univ _) h, by
        simp [Pi.single_apply, ite_smul]⟩
    have := (intPts a b).sub_mem (hcone _ h1).1 (hPH _ sum_gen_mem)
    simpa using this
  set H := intPts a b
  let PH : Finset H := (parallelepipedFinset g d).subtype (· ∈ H)
  let vH : ι → H := fun j => ⟨gen g d j, hgenH j⟩
  let degH : H →+ ℤ := (degHom n).comp H.subtype
  let LH : H →+ ℤ := intWeight a b
  have hmemPH : ∀ p : H, p ∈ PH ↔ (p : Lattice n) ∈ parallelepipedFinset g d :=
    fun p => Finset.mem_subtype
  have hval_sum : ∀ (p : H) (k : ι → ℕ),
      ((p + ∑ j, k j • vH j : H) : Lattice n) = p + ∑ j, k j • gen g d j := by
    intro p k
    simp [vH]
  have hsumv : ((∑ j, vH j : H) : Lattice n) = ∑ j, gen g d j := by simp [vH]
  have hconeH : ∀ x : H, x ∈ coneSet PH vH Finset.univ ↔
      (x : Lattice n) ∈ coneSet (parallelepipedFinset g d) (gen g d) Finset.univ := by
    intro x
    constructor
    · rintro ⟨p, hp, k, hk, rfl⟩
      exact ⟨p, (hmemPH p).mp hp, k, hk, hval_sum p k⟩
    · rintro ⟨p, hp, k, hk, hx⟩
      refine ⟨⟨p, hPH p hp⟩, (hmemPH _).mpr hp, k, hk, Subtype.ext ?_⟩
      rw [hval_sum]
      exact hx
  have hseries : series A PH vH degH LH Finset.univ = latticeSeries A (openSimplex w) wt := by
    ext m
    simp only [series, latticeSeries, PowerSeries.coeff_mk]
    by_cases hm : m = 0
    · subst hm
      have hempty : level PH vH degH Finset.univ ((0 : ℕ) : ℤ) = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨hx, hdeg⟩
        have h1 := (hcone _ ((hconeH x).mp hx)).2.1
        have h0 : (x : Lattice n).2 = 0 := hdeg
        omega
      rw [hempty, finsum_mem_empty]
      simp
    · simp only [hm, ↓reduceIte]
      have hlev : {y : Fin n → ℤ | (fun i => (y i : ℚ) / m) ∈ openSimplex w} =
          (fun x : H => (x : Lattice n).1) '' level PH vH degH Finset.univ (m : ℤ) := by
        ext y
        constructor
        · intro hy
          have hx : ((y, (m : ℤ)) : Lattice n) ∈
              coneSet (parallelepipedFinset g d) (gen g d) Finset.univ :=
            (mem_coneSet_iff _).mpr ((cone_iff_simplex hd hg y hm).mpr hy)
          exact ⟨⟨_, (hcone _ hx).1⟩, ⟨(hconeH _).mpr hx, rfl⟩, rfl⟩
        · rintro ⟨x, ⟨hx, hdeg⟩, rfl⟩
          have hx' := (hconeH x).mp hx
          have h2 : (x : Lattice n).2 = m := hdeg
          have hxe : (((x : Lattice n).1, (m : ℤ)) : Lattice n) = (x : Lattice n) :=
            Prod.ext rfl h2.symm
          rw [← hxe] at hx'
          exact (cone_iff_simplex hd hg _ hm).mp ((mem_coneSet_iff _).mp hx')
      rw [hlev, finsum_mem_image]
      · refine finsum_mem_congr rfl fun x hx => ?_
        obtain ⟨hx, hdeg⟩ := hx
        have h2 : (x : Lattice n).2 = m := hdeg
        have he := (hcone _ ((hconeH x).mp hx)).2.2
        rw [h2, Int.toNat_natCast] at he
        have hL : LH x = wt (x : Lattice n).1 m := by
          have := (intWeight_spec a b x).trans he
          exact_mod_cast this
        simp only [weight, hL]
      · intro x hx x' hx' h
        exact Subtype.ext (Prod.ext h (hx.2.trans hx'.2.symm))
  rw [← hseries]
  refine hasLimit_series A PH vH degH LH ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp p' hp' k k' h
    have := param_injective hLI p ((hmemPH p).mp hp) p' ((hmemPH p').mp hp') k k'
      (by rw [← hval_sum, ← hval_sum, h])
    exact ⟨Subtype.ext this.1, this.2⟩
  · exact fun j => deg_gen_pos (g := g) hd j
  · intro p hp
    show 0 ≤ degHom n (p : Lattice n)
    exact deg_nonneg (g := g) (d := d) (p : Lattice n) ((hmemPH p).mp hp)
  · exact (hmemPH _).mpr (by rw [hsumv]; exact sum_gen_mem)
  · intro p hp
    show degHom n (p : Lattice n) ≤ degHom n ((∑ j, vH j : H) : Lattice n)
    rw [hsumv]
    exact deg_le_top (g := g) (d := d) (p : Lattice n) ((hmemPH p).mp hp)
  · intro p hp hdeg
    apply Subtype.ext
    rw [hsumv]
    refine eq_top_of_deg_eq (g := g) hd (p : Lattice n) ((hmemPH p).mp hp) ?_
    have : degHom n (p : Lattice n) = degHom n ((∑ j, vH j : H) : Lattice n) := hdeg
    rw [hsumv] at this
    exact this

end cone

/-- **The series of an open rational simplex, rational weight coefficients.** -/
theorem hasLimit_openSimplex_rat {ι : Type*} [Fintype ι] [Nonempty ι] (w : ι → Fin n → ℚ)
    (hw : AffineIndependent ℚ w) (a : Fin n → ℚ) (b : ℚ) (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (x : Fin n → ℤ) (m : ℕ), (fun i => (x i : ℚ) / m) ∈ openSimplex w →
      (wt x m : ℚ) = ∑ i, a i * x i + b * m) :
    HasLimit A (latticeSeries A (openSimplex w) wt) ((-1) ^ Fintype.card ι) := by
  classical
  let d : ι → ℕ := fun j => ∏ i, (w j i).den
  let g : ι → Fin n → ℤ := fun j i => (w j i * d j).num
  have hd : ∀ j, 0 < d j := fun j => Finset.prod_pos fun i _ => Rat.den_pos _
  have hg : ∀ j i, (g j i : ℚ) = d j * w j i := fun j i => by
    rw [mul_comm]
    exact num_mul_cast _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  exact hasLimit_openSimplex_of_generators_rat A hw hd hg a b wt hwt

theorem hasLimit_of_triangulation_rat {κ : Type*} [Fintype κ] (ι : κ → Type*)
    [∀ k, Fintype (ι k)] [∀ k, Nonempty (ι k)] (w : ∀ k, ι k → Fin n → ℚ)
    (hw : ∀ k, AffineIndependent ℚ (w k))
    (hdisj : Pairwise (Function.onFun Disjoint fun k => openSimplex (w k)))
    (a : κ → Fin n → ℚ) (b : κ → ℚ) (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (k : κ) (x : Fin n → ℤ) (m : ℕ), (fun i => (x i : ℚ) / m) ∈ openSimplex (w k) →
      (wt x m : ℚ) = ∑ i, a k i * x i + b k * m) :
    HasLimit A (latticeSeries A (⋃ k, openSimplex (w k)) wt)
      (∑ k, (-1) ^ Fintype.card (ι k)) := by
  rw [latticeSeries_iUnion A _ hdisj fun k => ⟨_, openSimplex_bounded (w k)⟩]
  exact HasLimit.sum A Finset.univ _ _ fun k _ =>
    hasLimit_openSimplex_rat A (w k) (hw k) (a k) (b k) wt (hwt k)

end DiamondIntegral.Section8.SimplexSeries

namespace DiamondIntegral.Section8.Prism

open SimplexSeries HeightChains RationalSeries

variable {n : ℕ}

theorem Triangulation.hasLimit_rat {R : Type*} [CommRing R] (A : Rˣ) {D : Set (Fin n → ℚ)}
    (T : Triangulation n D) (wt : (Fin n → ℤ) → ℕ → ℤ) (a : T.κ → Fin n → ℚ) (b : T.κ → ℚ)
    (hwt : ∀ (k : T.κ) (x : Fin n → ℤ) (m : ℕ),
      (fun i => (x i : ℚ) / m) ∈ openSimplex (T.vert k) →
        (wt x m : ℚ) = ∑ i, a k i * x i + b k * m) :
    HasLimit A (latticeSeries A D wt) (-(T.eulerChar : R)) := by
  have h := hasLimit_of_triangulation_rat A (fun k => Fin (T.dim k + 1)) T.vert T.indep
    (fun k k' hkk' => T.disjoint k k' hkk') a b wt hwt
  rw [T.cover] at h
  have hc : (∑ k, (-1 : R) ^ Fintype.card (Fin (T.dim k + 1))) = -(T.eulerChar : R) := by
    simp only [Fintype.card_fin, Triangulation.eulerChar, pow_succ, mul_neg, mul_one,
      Finset.sum_neg_distrib]
    push_cast
    rfl
  rw [hc] at h
  exact h

/-- **Lemma 8.5.2 of Hrushovski–Loeser over `ℚ`, rational weight coefficients.** -/
theorem hasLimit_latticeSeries_rat {R : Type*} [CommRing R] (A : Rˣ) (G : List (AffFun n)) {N : ℚ}
    (hN : 0 ≤ N) {D : Set (Fin n → ℚ)} (hsub : D ⊆ box n N) (hD : Constructible G D)
    {ρ : Type*} (P : ρ → Set (Fin n → ℚ)) (hP : ∀ r, Constructible G (P r))
    (hcov : D ⊆ ⋃ r, P r) (a : ρ → Fin n → ℚ) (b : ρ → ℚ) (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (r : ρ) (x : Fin n → ℤ) (m : ℕ), (fun i => (x i : ℚ) / m) ∈ D ∩ P r →
      (wt x m : ℚ) = ∑ i, a r i * x i + b r * m)
    (T : Triangulation n D) : HasLimit A (latticeSeries A D wt) (-(T.eulerChar : R)) := by
  obtain ⟨T', hT', -⟩ := exists_triangulation_of_constructible G N hN D hsub hD
  rw [eulerChar_eq T T']
  have hmem : ∀ k, openSimplex (T'.vert k) ⊆ D := fun k x hx => by
    rw [← T'.cover]
    exact Set.mem_iUnion.mpr ⟨k, hx⟩
  have hr : ∀ k, ∃ r, openSimplex (T'.vert k) ⊆ P r := by
    intro k
    have hx : (fun i => ∑ j, (1 : ℚ) / Fintype.card (Fin (T'.dim k + 1)) * T'.vert k j i) ∈
        openSimplex (T'.vert k) :=
      (mem_openSimplex_iff _ _).mpr ⟨_, isBary_barycentre, fun _ => rfl⟩
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp (hcov (hmem k hx))
    exact ⟨r, fun y hy => (hP r _ y fun g hg => hT' k g hg _ hx y hy).mp hr⟩
  choose r hr using hr
  exact T'.hasLimit_rat A wt (fun k => a (r k)) (fun k => b (r k)) fun k x m hx =>
    hwt (r k) x m ⟨hmem k hx, hr k hx⟩

end DiamondIntegral.Section8.Prism

namespace DiamondIntegral.Section8.GammaCells

open Prism
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 GammaOrderLogic
open DiamondIntegral.Section2.GammaStable

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

local notation "Γ" => Values.Gamma (M := M)

/-- **Lemma 8.9 over the value group, rational weight coefficients.** -/
theorem hasLimit_gamma_rat (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) (R : Set M) (hr : Cardinal.mk R < κ)
    {π : Γ} (hπ1 : 1 < π) (hπ : GammaDefinableClosureAtBase ⟨R, ∅⟩ π)
    (hΔ : ∀ δ ∈ substructureValues (Substructure.closure LRV R), ∃ q : ℚ, δ = qpow π q)
    {n : ℕ} (X : Set (Fin n → Γ)) (hX : GammaDefinable ⟨R, ∅⟩ X) (N : ℕ)
    (hbd : ∀ z ∈ X, ∀ i, π ^ (-(N : ℤ)) ≤ z i ∧ z i ≤ π ^ (N : ℤ))
    {ρ : Type} [Fintype ρ] (P : ρ → Set (Fin n → Γ)) (hP : ∀ r, GammaDefinable ⟨R, ∅⟩ (P r))
    (hcov : X ⊆ ⋃ r, P r) (a : ρ → Fin n → ℚ) (b : ρ → ℚ) (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (r : ρ) (x : Fin n → ℤ) (m : ℕ),
      (fun i => (x i : ℚ) / m) ∈ ratTrace π X ∩ ratTrace π (P r) →
        (wt x m : ℚ) = ∑ i, a r i * x i + b r * m)
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
  exact hasLimit_latticeSeries_rat A G (Nat.cast_nonneg N) hsub (constructible_mono hD hG₀)
    (fun r => ratTrace π (P r)) (fun r => constructible_mono (hGP r) (hGr r)) hcovQ a b wt hwt T

end DiamondIntegral.Section8.GammaCells

namespace DiamondIntegral.Section8.PuiseuxValues

open Classical FirstOrder FirstOrder.Language HahnSeries
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.GammaCells DiamondIntegral.Section4 GammaOrderLogic

variable (P : PuiseuxAmbient)

/-- **Lemma 8.9 in the Puiseux ambient, rational weight coefficients.** As `lemma_8_9`, with
`wt x m = a_r · x + b_r m` for rational `a_r`, `b_r`; `wt` is integral by its type. -/
theorem lemma_8_9_rat {n : ℕ} (X : Set (Fin n → Values.Gamma (M := P.N)))
    (hX : GammaDefinable ⟨(P.G.real : Set P.N), ∅⟩ X) (N : ℕ)
    (hbd : ∀ z ∈ X, ∀ i, uniformizerValue P ^ (-(N : ℤ)) ≤ z i ∧ z i ≤ uniformizerValue P ^ (N : ℤ))
    {ρ : Type} [Fintype ρ] (Pc : ρ → Set (Fin n → Values.Gamma (M := P.N)))
    (hP : ∀ r, GammaDefinable ⟨(P.G.real : Set P.N), ∅⟩ (Pc r))
    (hcov : X ⊆ ⋃ r, Pc r) (a : ρ → Fin n → ℚ) (b : ρ → ℚ) (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (r : ρ) (x : Fin n → ℤ) (m : ℕ),
      (fun i => (x i : ℚ) / m) ∈ ratTrace (uniformizerValue P) X ∩
        ratTrace (uniformizerValue P) (Pc r) → (wt x m : ℚ) = ∑ i, a r i * x i + b r * m)
    {R : Type*} [CommRing R] (A : Rˣ) :
    RationalSeries.HasLimit A
      (SimplexSeries.latticeSeries A (ratTrace (uniformizerValue P) X) wt)
      (-((GammaIteratedIntegral.integrateAll P.G.model00 P.G.uncountable.le P.G.saturated
        ⟨(P.G.real : Set P.N), ∅⟩ P.G.small_real
        (by simpa using Cardinal.aleph0_pos.trans P.G.uncountable) EulerKind.geometric n
          (GammaIndicators.indicatorFamily ⟨(P.G.real : Set P.N), ∅⟩ X hX) : ℤ) : R)) :=
  hasLimit_gamma_rat P.hc P.G.model00 P.G.uncountable P.G.saturated P.G.homogeneous
    (P.G.real : Set P.N) P.G.small_real (one_lt_uniformizerValue P)
    (uniformizerValue_definable P) (substructureValues_rational P) X hX N hbd Pc hP hcov a b wt
    hwt A

end DiamondIntegral.Section8.PuiseuxValues
