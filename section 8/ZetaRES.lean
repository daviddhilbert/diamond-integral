import «section 8».ZetaPieces

/-! `h_m` of an RES chart, for Theorem 8.11.

An RES chart `V` has finitely many value tuples (`codes_finite`), all rational, so `V` is its own
lattice part at some level `m₀` (`res_level`) and its weight takes finitely many values. Hence the
pairs `(c, w)` of a value tuple and a weight occurring on `V` form a finite set `pairFin V`,
independent of `m`. With `V_{c,w}` the piece of value tuple `c` and weight `w`,

* `res_class`: `[V] = Σ_{(c,w)} [V_{c,w}]`;
* `hm_res`: `h_m([V]) = Σ_{(c,w), c ∈ Λ_m} T^{-m w} Θ([V_{c,w}])`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Hm

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts RVVolumeMaps FiniteTupleBlocks
open DiamondIntegral.Section8.GammaCells DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.ValueMaps
open DiamondIntegral.Section8.RESPieces
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open GammaOrderLogic GammaDefinableMaps GammaRVChartPresentation

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

theorem inLattice_qpow_of_dvd (q : ℚ) {m : ℕ} (h : q.den ∣ m) : InLattice π m (qpow π q) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨q.num * k, by rw [pow_mul, qpow_pow_den, zpow_mul, zpow_natCast]⟩

variable {r : ℕ} (V : RESChart (base P) r)

theorem codes_finite : (codeValues '' V.domain).Finite := by
  refine (V.finite_values.image (fun p i => RVMeasuredBounds.finiteValue (p i))).subset ?_
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨V.valuePattern ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩, ?_⟩
  funext i
  exact RVMeasuredBounds.finiteValue_vrv _

theorem code_definable {v : Fin V.arity → P.N} (hv : v ∈ V.domain) (i : Fin V.arity) :
    GammaDefinableClosureAtBase (base P) (codeValue (v i)) := by
  have hfin : ((fun u : Fin V.arity → P.N => codeValue (u i)) '' V.domain).Finite :=
    ((codes_finite P V).image (fun c => c i)).subset (by
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨codeValues u, ⟨u, hu, rfl⟩, rfl⟩)
  refine gamma_finset_element_definable_base (base P) hfin.toFinset ?_ _
    (hfin.mem_toFinset.mpr ⟨v, hv, rfl⟩)
  rw [hfin.coe_toFinset]
  exact image_definable (base P) (coord_volume_definable (base P) V.domain_definable i)

/-- **`V` is its own lattice part at some level.** -/
theorem res_level : ∃ m₀ : ℕ+, ∀ v ∈ V.domain, ∀ i, InLattice π m₀ (codeValue (v i)) := by
  let Q : Set Γ := ⋃ i : Fin V.arity, (fun u : Fin V.arity → P.N => codeValue (u i)) '' V.domain
  have hQ : Q.Finite := Set.finite_iUnion fun i =>
    ((codes_finite P V).image (fun c => c i)).subset (by
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨codeValues u, ⟨u, hu, rfl⟩, rfl⟩)
  have hrat : ∀ x ∈ Q, ∃ q : ℚ, x = qpow π q := by
    intro x hx
    obtain ⟨i, u, hu, rfl⟩ := Set.mem_iUnion.mp hx
    exact definable_point_rational P (code_definable P V hu i)
  choose! q hq using hrat
  let m₀ : ℕ := ∏ x ∈ hQ.toFinset, (q x).den
  have hm₀ : 0 < m₀ := Finset.prod_pos fun x _ => (q x).den_pos
  refine ⟨⟨m₀, hm₀⟩, fun v hv i => ?_⟩
  have hx : codeValue (v i) ∈ Q := Set.mem_iUnion.mpr ⟨i, v, hv, rfl⟩
  rw [hq _ hx]
  exact inLattice_qpow_of_dvd P _ (Finset.dvd_prod_of_mem _ (hQ.mem_toFinset.mpr hx))

/-- A level at which `V` is its own lattice part. -/
def m₀ : ℕ+ := (res_level P V).choose

theorem m₀_spec : ∀ v ∈ V.domain, ∀ i, InLattice π (m₀ P V) (codeValue (v i)) :=
  (res_level P V).choose_spec

/-- The pairs `(c, w)` of a value tuple and a weight occurring on `V`. -/
def pairs : Set ((Fin V.arity → Γ) × Γ) := (fun v => (codeValues v, V.correctedWeight v)) '' V.domain

theorem pairs_finite : (pairs P V).Finite := by
  refine ((codes_finite P V).prod
    (latticeWeights_finite P (RVBoundedCharts.ofRES V) (m₀ P V).ne_zero)).subset ?_
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨⟨v, hv, rfl⟩, v, ⟨hv, m₀_spec P V v hv⟩, rfl⟩

def pairFin : Finset ((Fin V.arity → Γ) × Γ) := (pairs_finite P V).toFinset

theorem mem_pairFin (p : (Fin V.arity → Γ) × Γ) :
    p ∈ pairFin P V ↔ ∃ v ∈ V.domain, codeValues v = p.1 ∧ V.correctedWeight v = p.2 := by
  simp only [pairFin, Set.Finite.mem_toFinset, pairs, Set.mem_image, Prod.ext_iff]

theorem pair_code_definable {p : (Fin V.arity → Γ) × Γ} (hp : p ∈ pairFin P V) (i : Fin V.arity) :
    GammaDefinableClosureAtBase (base P) (p.1 i) := by
  obtain ⟨v, hv, hc, -⟩ := (mem_pairFin P V p).mp hp
  rw [← hc]
  exact code_definable P V hv i

theorem pair_weight_definable {p : (Fin V.arity → Γ) × Γ} (hp : p ∈ pairFin P V) :
    GammaDefinableClosureAtBase (base P) p.2 := by
  obtain ⟨v, hv, -, hw⟩ := (mem_pairFin P V p).mp hp
  rw [← hw]
  exact latticeWeight_definable P (RVBoundedCharts.ofRES V) (m₀ P V).ne_zero ⟨v, ⟨hv, m₀_spec P V v hv⟩, rfl⟩

theorem pair_weight_rational {p : (Fin V.arity → Γ) × Γ} (hp : p ∈ pairFin P V) :
    IsRationalValue π p.2 := by
  obtain ⟨q, hq⟩ := definable_point_rational P (pair_weight_definable P V hp)
  rw [hq]
  exact isRationalValue_qpow π q

/-- The piece of value tuple `c` and weight `w`. -/
def resPiece (p : (Fin V.arity → Γ) × Γ) : Set (Fin V.arity → P.N) :=
  {v | v ∈ V.domain ∧ codeValues v = p.1 ∧ V.correctedWeight v = p.2}

theorem codes_set_definable (c : Fin V.arity → Γ)
    (hc : ∀ i, GammaDefinableClosureAtBase (base P) (c i)) (s : Finset (Fin V.arity)) :
    DefinableOverBase (base P) (fun _ : Fin V.arity => .rv)
      {v | v ∈ V.domain ∧ ∀ i ∈ s, codeValue (v i) = c i} := by
  induction s using Finset.induction_on with
  | empty =>
    convert V.domain_definable using 1
    ext v
    simp
  | insert j s hj ih =>
    have h := preimage_definable (base P) ih (volume_restrict (base P)
      (coord_volume_definable (base P) V.domain_definable j) ih (fun _ h => h.1))
      (show GammaDefinableOverBase (base P) {c j} from (hc j))
    convert h using 1
    ext v
    simp only [Finset.mem_insert, forall_eq_or_imp, Set.mem_setOf_eq, Set.mem_singleton_iff]
    tauto

theorem resPiece_definable {p : (Fin V.arity → Γ) × Γ} (hp : p ∈ pairFin P V) :
    DefinableOverBase (base P) (fun _ : Fin V.arity => .rv) (resPiece P V p) := by
  have h0 := codes_set_definable P V p.1 (pair_code_definable P V hp) Finset.univ
  have h := preimage_definable (base P) h0 (volume_restrict (base P)
    (weight_volume_definable (base P) V.toChart) h0 (fun _ h => h.1))
    (show GammaDefinableOverBase (base P) {p.2} from pair_weight_definable P V hp)
  convert h using 1
  ext v
  simp only [resPiece, Finset.mem_univ, true_implies, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, fun i => congrFun h2 i⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, funext h2, h3⟩

theorem resPieces_disjoint (S : Finset ((Fin V.arity → Γ) × Γ)) :
    (S : Set ((Fin V.arity → Γ) × Γ)).PairwiseDisjoint (resPiece P V) := by
  intro p _ q _ hpq
  rw [Function.onFun, Set.disjoint_left]
  rintro v ⟨-, h1, h2⟩ ⟨-, h1', h2'⟩
  exact hpq (Prod.ext (h1.symm.trans h1') (h2.symm.trans h2'))

theorem domain_eq_pieces : V.domain = ⋃ p ∈ pairFin P V, resPiece P V p := by
  ext v
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · intro hv
    exact ⟨(codeValues v, V.correctedWeight v), (mem_pairFin P V _).mpr ⟨v, hv, rfl, rfl⟩, hv, rfl, rfl⟩
  · rintro ⟨p, -, hv, -⟩
    exact hv

/-- **`[V] = Σ [V_{c,w}]`.** -/
theorem res_class :
    nativeRESChartClass V = ∑ p ∈ pairFin P V, classOn V (resPiece P V p) := by
  rw [← classOn_domain, domain_eq_pieces P V]
  exact classOn_biUnion _ _ _ (fun p hp => resPiece_definable P V hp) (fun p _ v hv => hv.1)
    (resPieces_disjoint P V _)

variable (m : ℕ+)

/-- The pairs whose value tuple is a lattice point. -/
def pairLat : Finset ((Fin V.arity → Γ) × Γ) :=
  (pairFin P V).filter fun p => ∀ i, InLattice π m (p.1 i)

theorem pairLat_sub {p : (Fin V.arity → Γ) × Γ} (hp : p ∈ pairLat P V m) : p ∈ pairFin P V :=
  (Finset.mem_filter.mp hp).1

theorem res_fibre (w : Γ) :
    latticeFibre P V.toChart m w = ⋃ p ∈ (pairLat P V m).filter (fun p => p.2 = w), resPiece P V p := by
  ext v
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter, pairLat]
  constructor
  · rintro ⟨⟨hv, hl⟩, hw⟩
    exact ⟨(codeValues v, w), ⟨⟨(mem_pairFin P V _).mpr ⟨v, hv, rfl, hw⟩, hl⟩, rfl⟩, hv, rfl, hw⟩
  · rintro ⟨p, ⟨⟨-, hl⟩, rfl⟩, hv, hc, hw⟩
    refine ⟨⟨hv, fun i => ?_⟩, hw⟩
    rw [show codeValue (v i) = p.1 i from congrFun hc i]
    exact hl i

/-- **`h_m` of an RES chart.** -/
theorem hm_res (hb : RVMeasuredBounds.DomainBounded V.toChart) :
    hmValue P V.toChart hb m =
      ∑ p ∈ pairLat P V m, AddMonoidAlgebra.single (-(m : ℚ) * ratValue π p.2)
        (theta P (classOn V (resPiece P V p))) := by
  refine hmValue_decomp P _ _ m (pairLat P V m) Prod.snd (fun p => classOn V (resPiece P V p))
    (fun w => ?_) (fun w hw => ?_)
  · rw [← classOn_domain, fibreChart_domain, res_fibre,
      classOn_biUnion (fibreChart P V.toChart hb m w) ((pairLat P V m).filter (fun p => p.2 = w))
        (resPiece P V)
      (fun p hp => resPiece_definable P V (pairLat_sub P V m (Finset.mem_filter.mp hp).1))
      (fun p hp => ?_) (resPieces_disjoint P V _)]
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := pairLat_sub P V m (Finset.mem_filter.mp hp).1
      have hsub : resPiece P V p ⊆ (fibreChart P V.toChart hb m w).domain := fun v hv => by
        rw [fibreChart_domain, res_fibre]
        exact Set.mem_biUnion hp hv
      rw [classOn_eq (fibreChart P V.toChart hb m w) _ (resPiece_definable P V hp') hsub,
        classOn_eq V _ (resPiece_definable P V hp') (fun v hv => hv.1)]
      exact class_eq_of_domain _ _ rfl fun u => by simp only [Fin.cast_refl, Function.comp_id]; rfl
    · intro v hv
      rw [fibreChart_domain, res_fibre]
      exact Set.mem_biUnion hp hv
  · obtain ⟨v, hv⟩ := (mem_weights P _ _ m w).mp hw
    rw [res_fibre] at hv
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter] at hv
    obtain ⟨p, ⟨hp, hpw⟩, -⟩ := hv
    exact ⟨p, hp, hpw⟩

end DiamondIntegral.Section8.Hm
