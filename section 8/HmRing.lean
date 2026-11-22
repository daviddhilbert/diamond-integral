import «section 8».HmProduct
import FubiniTheorems.Fubini.NativePrincipalChartBridge

/-! The ring homomorphism `h_m : K μRV^db[*] → K^μ̂ Var_ℂ[[𝔸]⁻¹][T^ℚ]`.

The value `hmValue` on bounded charts satisfies the relations of the disjoint-union presentation of
the library: invariance under isomorphisms (`hmValue_iso`), additivity on tagged coproducts
(`hmValue_coproduct`, from additivity on disjoint unions, multiplicativity and the value `1` of the
one-point tag charts), the unit, multiplicativity and vanishing on empty charts. So it defines a
ring homomorphism `hm P m` with `hm P m [a] = hmValue a` (`hm_objectClass`): Lemma 8.2 of the
paper, with the formula of the lemma as the definition. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Hm

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts FiniteTupleBlocks
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal DiamondIntegral.Section8.PuiseuxValues
open RVMeasuredProduct RVMeasuredProductProperties RVChartDisjointUnion RVNamedTuples RVTaggedCoproduct

variable (P : PuiseuxAmbient)

local notation "π" => uniformizerValue P

theorem finite_bounded {k : ℕ} (a : Chart (base P) k) (h : a.domain.Finite) :
    RVMeasuredBounds.DomainBounded a :=
  RVMeasuredBounds.finite_patterns_bounded a (a.finite_domain_values h)

theorem tagZero_bounded : RVMeasuredBounds.DomainBounded (tagZero (base P)) :=
  finite_bounded P _ (Set.finite_singleton _)

theorem tagOne_bounded : RVMeasuredBounds.DomainBounded (tagOne (base P)) :=
  finite_bounded P _ (Set.finite_singleton _)

theorem zeros_bounded (n : ℕ) : RVMeasuredBounds.DomainBounded (zeros (base P) n) :=
  finite_bounded P _ (Set.finite_singleton _)

theorem codeValue_zero : codeValue (iRVZero : P.N) = 1 := by
  have h : ¬ NonzeroRV (iRVZero : P.N) := fun h => h.2 rfl
  simp only [codeValue, h, ↓reduceDIte]

theorem hmValue_tagZero (h : RVMeasuredBounds.DomainBounded (tagZero (base P))) (m : ℕ+) :
    hmValue P (tagZero (base P)) h m = 1 :=
  hmValue_tuple P _ _ h m fun i => by
    fin_cases i
    change InLattice π m (codeValue (iRVZero : P.N))
    rw [codeValue_zero]; exact inLattice_one _ _

theorem hmValue_tagOne (h : RVMeasuredBounds.DomainBounded (tagOne (base P))) (m : ℕ+) :
    hmValue P (tagOne (base P)) h m = 1 :=
  hmValue_tuple P _ _ h m fun i => by
    fin_cases i
    change InLattice π m (codeValue (iRVOne : P.N))
    rw [nativeCodeValue_one]; exact inLattice_one _ _

theorem hmValue_zeros (n : ℕ) (h : RVMeasuredBounds.DomainBounded (zeros (base P) n)) (m : ℕ+) :
    hmValue P (zeros (base P) n) h m = 1 :=
  hmValue_tuple P _ _ h m fun i => by
    change InLattice π m (codeValue (iRVZero : P.N))
    rw [codeValue_zero]; exact inLattice_one _ _

theorem bounded_of_domain_eq {k l : ℕ} {a : Chart (base P) k} {b : Chart (base P) l}
    (h : a.arity = b.arity) (hd : ∀ u : Fin a.arity → P.N, u ∈ a.domain ↔ u ∘ Fin.cast h.symm ∈ b.domain)
    (hb : RVMeasuredBounds.DomainBounded b) : RVMeasuredBounds.DomainBounded a := by
  obtain ⟨β, hβ⟩ := hb
  refine ⟨β, fun u hu i hi => ?_⟩
  have := hβ _ ((hd u).mp hu) (Fin.cast h i) (by simpa using hi)
  simpa using this

/-- **`h_m` is additive on tagged coproducts.** -/
theorem hmValue_coproduct {k : ℕ} (a b : Chart (base P) k) (ha : RVMeasuredBounds.DomainBounded a)
    (hb : RVMeasuredBounds.DomainBounded b) (hc : RVMeasuredBounds.DomainBounded (coproduct a b))
    (m : ℕ+) : hmValue P (coproduct a b) hc m = hmValue P a ha m + hmValue P b hb m := by
  have hL1 := product_domain_bounded _ _ (tagZero_bounded P) ha
  have hL2 := product_domain_bounded _ _ hL1 (zeros_bounded P b.arity)
  have hR1 := product_domain_bounded _ _ (tagOne_bounded P) (zeros_bounded P a.arity)
  have hR2 := product_domain_bounded _ _ hR1 hb
  have hL : RVMeasuredBounds.DomainBounded (leftData a b).toChart :=
    bounded_of_domain_eq P (a := (leftData a b).toChart)
      (b := product (product (tagZero (base P)) a) (zeros (base P) b.arity)) rfl (fun u => by
      simp only [Fin.cast_refl, Function.comp_id]
      change u ∈ (leftData a b).domain ↔ u ∈ (product (product (tagZero (base P)) a) (zeros (base P) b.arity)).domain
      rw [leftData, castGrade_domain]; rfl) hL2
  have hR : RVMeasuredBounds.DomainBounded (rightData a b).toChart := hR2
  change hmValue P (disjointUnion (leftData a b) (rightData a b) (tagged_disjoint a b)).toChart hc m = _
  rw [hmValue_union P _ _ _ hc hL hR]
  congr 1
  · change hmValue P (castGrade (Nat.zero_add k) (leftRawData a b)).toChart hL m = _
    rw [hmValue_castGrade P (Nat.zero_add k) (leftRawData a b) hL hL2]
    change hmValue P (product (product (tagZero (base P)) a) (zeros (base P) b.arity)) hL2 m = _
    rw [hmValue_product P _ _ hL1 (zeros_bounded P b.arity) hL2,
      hmValue_product P _ _ (tagZero_bounded P) ha hL1, hmValue_tagZero, hmValue_zeros, one_mul, mul_one]
  · change hmValue P (product (product (tagOne (base P)) (zeros (base P) a.arity)) b) hR2 m = _
    rw [hmValue_product P _ _ hR1 hb hR2,
      hmValue_product P _ _ (tagOne_bounded P) (zeros_bounded P a.arity) hR1, hmValue_tagOne,
      hmValue_zeros, one_mul, one_mul]

/-- `h_m` as an invariant of the disjoint-union presentation of `K μRV^db[*]`. -/
def hmInvariant (m : ℕ+) :
    RVFamilyDisjointPresentation.Invariant (RVBoundedDisjointPresentation.family (base P))
      (PuiseuxPolynomial EquivariantVariety.ModifiedRing) where
  value _ a ha := hmValue P a ha m
  iso _ _ _ ha hb F := hmValue_iso P ha hb F m
  coproduct _ a b ha hb := hmValue_coproduct P a b ha hb _ m
  unit := hmValue_unit P _ m
  product _ _ a b ha hb := hmValue_product P a b ha hb _ m
  empty _ a ha h := hmValue_empty P a ha m h

/-- **The ring homomorphism `h_m`** (Lemma 8.2). -/
def hm (m : ℕ+) : RVBoundedRing.Ring (base P) →+* PuiseuxPolynomial EquivariantVariety.ModifiedRing :=
  (RVFamilyDisjointPresentation.lift _ (hmInvariant P m)).comp
    (RVBoundedDisjointPresentation.fromChartRing (base P))

/-- `h_m` on the class of a bounded chart is given by the formula of Lemma 8.2. -/
theorem hm_objectClass (m : ℕ+) {k : ℕ} (a : RVBoundedCharts.BoundedChart (base P) k) :
    hm P m (RVBoundedRing.objectClass a) = hmValue P a.toChart a.domain_bounded m := by
  change RVFamilyDisjointPresentation.lift _ _ (RVBoundedDisjointPresentation.fromChartRing (base P)
    (RVBoundedRing.objectClass a)) = _
  rw [RVBoundedDisjointPresentation.fromChartRing_class]
  exact RVFamilyDisjointPresentation.lift_objectClass _ _ _

end DiamondIntegral.Section8.Hm
