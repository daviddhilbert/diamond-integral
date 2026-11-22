import «section 8».HmAnnular
import «section 8».GraphSeries
import FubiniTheorems.Prerequisites.Euler.RESAllBoundedFiniteBalancing
import FubiniTheorems.Prerequisites.Euler.GammaBoundedRVCharts

/-! `h_m` on the two factors of a product generator `[g♯ × V]`, for Theorem 8.11.

* **Sharp charts.** For a doubly bounded `Γ`-chart `g` with support `I` and weight
  `σ(δ) = vol(δ) ∏ δ_i`, the lattice part of `g♯` of weight `w` is the union of the fibres
  `{z | vrv z = δ}` over the lattice points `δ ∈ I` with `σ(δ) = w`; each fibre has the class of
  `[G_m]^ℓ` (`point_class`, from the library's balancing of finite `Γ`-charts). Hence
  `h_m([g♯]) = Σ_{δ ∈ I_m} T^{-m σ(δ)} Θ([G_m])^ℓ` (`hm_sharp`).
* **RES charts.** An RES chart `V` has finitely many value tuples, all rational, so it is its own
  lattice part at some level `m₀`, and its weight takes finitely many values. Its pieces
  `V_{c,w}` (value tuple `c`, weight `w`) do not depend on `m`, and
  `h_m([V]) = Σ_{(c,w), c ∈ Λ_m} T^{-m w} Θ([V_{c,w}])` (`hm_res`). -/

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

theorem hγ0 : Cardinal.mk (base P).gamma < P.G.κ := by
  simpa using Cardinal.aleph0_pos.trans P.G.uncountable

/-! ### Points of `Γ^ℓ` and torus powers -/

theorem point_definable {ℓ : ℕ} (δ : Fin ℓ → Γ)
    (hδ : ∀ i, GammaDefinableClosureAtBase (base P) (δ i)) :
    GammaDefinable (base P) ({δ} : Set (Fin ℓ → Γ)) := by
  have h := GammaQuantifierLogic.finite_iInter_definable_base (base P)
    (fun i : Fin ℓ => {z : Fin ℓ → Γ | z ∘ (fun _ : Fin 1 => i) ∈ {w : Fin 1 → Γ | w 0 ∈ ({δ i} : Set Γ)}})
    (fun i => GammaRelationLogic.preimage_definable_base (base P) _
      ((unary_definable_iff (base P) {δ i}).mpr (hδ i)) _)
  convert h using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq, Function.comp]
  exact ⟨fun h i => h ▸ rfl, fun h => funext h⟩

/-- The finite `Γ`-chart `{δ}`, with volume `1`. -/
def pointChart {ℓ : ℕ} (δ : Fin ℓ → Γ) (hδ : ∀ i, GammaDefinableClosureAtBase (base P) (δ i)) :
    GammaFiniteRVCharts.FiniteChart (base P) ℓ :=
  GammaFiniteRVCharts.ofTotal (base P) ℓ {δ} (point_definable P δ hδ) (Set.finite_singleton δ)
    (fun _ => 1) (constant_definable (base P) 1 (GammaGroupNames.one_definable_base _))

theorem pointChart_domain {ℓ : ℕ} (δ : Fin ℓ → Γ) (hδ : ∀ i, GammaDefinableClosureAtBase (base P) (δ i))
    (z : Fin ℓ → P.N) :
    z ∈ (GammaFiniteRVCharts.sharp (pointChart P δ hδ)).domain ↔ Proper z ∧ codeValues z = δ :=
  Iff.rfl

/-- **The class of `{z | vrv z = δ}` is `[G_m]^ℓ`.** -/
theorem point_class {ℓ : ℕ} (δ : Fin ℓ → Γ) (hδ : ∀ i, GammaDefinableClosureAtBase (base P) (δ i)) :
    nativeRESChartClass (GammaFiniteRVCharts.sharp (pointChart P δ hδ)) = nativeTorusClass (base P) ^ ℓ := by
  have h1 := RESAllBoundedFiniteBalancing.finite_balance P.hc P.G.model00
    Section5.GammaQE.gamma_piecewise_rational_affine P.G.uncountable.le P.G.saturated (base P)
    P.G.small_real (hγ0 P) (base_nontrivial P) EulerKind.geometric
  have h2 := RingHom.congr_fun h1 (GammaFiniteRVPresentation.objectClass (pointChart P δ hδ))
  rw [RESAllBoundedFiniteBalancing.gammaMap_class] at h2
  change RESOrdinaryReduction.forget _ (GammaFiniteRVMaps.sharp _
    (GammaFiniteRVPresentation.objectClass (pointChart P δ hδ))) = _ at h2
  rw [GammaFiniteRVMaps.sharp_class, RESOrdinaryReduction.forget_objectClass] at h2
  have hχ : GammaIteratedIntegral.integrateAll P.G.model00 P.G.uncountable.le P.G.saturated (base P)
      P.G.small_real (hγ0 P) EulerKind.geometric ℓ
      (GammaIndicators.indicatorFamily (base P) (pointChart P δ hδ).support
        (pointChart P δ hδ).support_definable) = 1 :=
    GammaPointFamilies.integrateAll_singleton P.G.model00 P.G.uncountable.le P.G.saturated (base P)
      P.G.small_real (hγ0 P) EulerKind.geometric ℓ _ δ 1 (fun z => by
        simp [GammaIndicators.indicatorFamily, pointChart, GammaFiniteRVCharts.ofTotal,
          GammaChartOperations.ofTotal])
  rw [hχ, Int.cast_one, one_mul] at h2
  rw [nativeRESChartClass, ← RESDimensionFreeReduction.fromGradedReduced_raw, h2, map_pow]
  rfl

/-! ### Sharp charts -/

section Sharp

variable {ℓ : ℕ} (g : GammaBoundedRVCharts.BoundedChart (base P) ℓ) (m : ℕ+)

/-- The weight `σ(δ) = vol(δ) ∏ δ_i` of `g`. -/
def sig (δ : Fin ℓ → Γ) : Γ := GammaWeightProfiles.correctedWeight g.volume δ

/-- The lattice points of the support. -/
def supLat : Set (Fin ℓ → Γ) := {δ | δ ∈ g.support ∧ ∀ i, InLattice π m (δ i)}

theorem supLat_finite : (supLat P g m).Finite := by
  obtain ⟨β, hβ⟩ := g.domain_bounded
  exact lattice_finite P m.ne_zero g.support g.support_definable β hβ

def supFin : Finset (Fin ℓ → Γ) := (supLat_finite P g m).toFinset

theorem mem_supFin (δ : Fin ℓ → Γ) : δ ∈ supFin P g m ↔ δ ∈ g.support ∧ ∀ i, InLattice π m (δ i) := by
  simp [supFin, supLat]

theorem supFin_definable {δ : Fin ℓ → Γ} (hδ : δ ∈ supFin P g m) (i : Fin ℓ) :
    GammaDefinableClosureAtBase (base P) (δ i) := by
  obtain ⟨z, hz⟩ := eq_qpow_of_inLattice m.ne_zero (((mem_supFin P g m δ).mp hδ).2 i)
  rw [hz]
  exact qpow_definable P _

/-- The fibre over `δ`. -/
def fib (δ : Fin ℓ → Γ) : Set (Fin ℓ → P.N) := {z | Proper z ∧ codeValues z = δ}

theorem sharp_lattice (z : Fin ℓ → P.N) :
    z ∈ latticeDomain P (GammaBoundedRVCharts.sharp g).toChart m ↔
      Proper z ∧ codeValues z ∈ supFin P g m := by
  rw [mem_supFin]
  exact ⟨fun ⟨⟨hp, hI⟩, hl⟩ => ⟨hp, hI, hl⟩, fun ⟨hp, hI, hl⟩ => ⟨⟨hp, hI⟩, hl⟩⟩

theorem sharp_fibre (w : Γ) :
    latticeFibre P (GammaBoundedRVCharts.sharp g).toChart m w =
      ⋃ δ ∈ (supFin P g m).filter (fun δ => sig P g δ = w), fib P δ := by
  ext z
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter]
  constructor
  · rintro ⟨hl, hw⟩
    obtain ⟨hp, hδ⟩ := (sharp_lattice P g m z).mp hl
    exact ⟨codeValues z, ⟨hδ, hw⟩, hp, rfl⟩
  · rintro ⟨δ, ⟨hδ, hw⟩, hp, rfl⟩
    exact ⟨(sharp_lattice P g m z).mpr ⟨hp, hδ⟩, hw⟩

theorem fib_class {δ : Fin ℓ → Γ} (hδ : δ ∈ supFin P g m) :
    classOn (fibreChart P (GammaBoundedRVCharts.sharp g).toChart
        (GammaBoundedRVCharts.sharp g).domain_bounded m (sig P g δ)) (fib P δ) =
      nativeTorusClass (base P) ^ ℓ := by
  rw [← point_class P δ (supFin_definable P g m hδ)]
  refine classOn_eq_of_domain _ _ ?_ ?_ _ rfl fun u => ?_
  · exact (GammaFiniteRVCharts.sharp (pointChart P δ (supFin_definable P g m hδ))).domain_definable
  · rintro z ⟨hp, hz⟩
    rw [fibreChart_domain]
    refine ⟨(sharp_lattice P g m z).mpr ⟨hp, hz ▸ hδ⟩, ?_⟩
    show sig P g (codeValues z) = sig P g δ
    rw [hz]
  · simp only [Fin.cast_refl, Function.comp_id]
    rfl

theorem fibs_disjoint (w : Γ) :
    (((supFin P g m).filter (fun δ => sig P g δ = w) : Finset _) : Set (Fin ℓ → Γ)).PairwiseDisjoint
      (fib P) := by
  intro δ _ δ' _ hne
  rw [Function.onFun, Set.disjoint_left]
  rintro z ⟨-, h1⟩ ⟨-, h2⟩
  exact hne (h1.symm.trans h2)

/-- **`h_m` of a sharp chart.** -/
theorem hm_sharp :
    hmValue P (GammaBoundedRVCharts.sharp g).toChart (GammaBoundedRVCharts.sharp g).domain_bounded m =
      ∑ δ ∈ supFin P g m, AddMonoidAlgebra.single (-(m : ℚ) * ratValue π (sig P g δ))
        (theta P (nativeTorusClass (base P) ^ ℓ)) := by
  refine hmValue_decomp P _ _ m (supFin P g m) (sig P g) (fun _ => nativeTorusClass (base P) ^ ℓ)
    (fun w => ?_) (fun w hw => ?_)
  · rw [← classOn_domain, fibreChart_domain, sharp_fibre, classOn_biUnion _ _ _
      (fun δ hδ => ?_) (fun δ hδ => ?_) (fibs_disjoint P g m w)]
    · refine Finset.sum_congr rfl fun δ hδ => ?_
      obtain ⟨hδ, hw⟩ := Finset.mem_filter.mp hδ
      rw [← hw]
      exact fib_class P g m hδ
    · exact (GammaFiniteRVCharts.sharp (pointChart P δ
        (supFin_definable P g m (Finset.mem_filter.mp hδ).1))).domain_definable
    · rintro z ⟨hp, rfl⟩
      rw [fibreChart_domain]
      exact ⟨(sharp_lattice P g m z).mpr ⟨hp, (Finset.mem_filter.mp hδ).1⟩, (Finset.mem_filter.mp hδ).2⟩
  · obtain ⟨z, hz⟩ := (mem_weights P _ _ m w).mp hw
    rw [sharp_fibre] at hz
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter] at hz
    obtain ⟨δ, ⟨hδ, hw⟩, -⟩ := hz
    exact ⟨δ, hδ, hw⟩

theorem fib_nonempty (δ : Fin ℓ → Γ) : (fib P δ).Nonempty := by
  choose t ht htv using fun i => EndpointLogic.codeValue_surjective (δ i)
  exact ⟨t, ht, funext htv⟩

/-- The weight of a lattice point of the support is rational. -/
theorem sig_rational {δ : Fin ℓ → Γ} (hδ : δ ∈ supFin P g m) : IsRationalValue π (sig P g δ) := by
  obtain ⟨z, hz⟩ := fib_nonempty P δ
  have hw : sig P g δ ∈ weights P (GammaBoundedRVCharts.sharp g).toChart
      (GammaBoundedRVCharts.sharp g).domain_bounded m := by
    refine (mem_weights P _ _ m _).mpr ⟨z, ?_⟩
    rw [sharp_fibre]
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter]
    exact ⟨δ, ⟨hδ, rfl⟩, hz⟩
  exact weight_rational P _ _ m hw

end Sharp

end DiamondIntegral.Section8.Hm
