import «section 5».InflatedRelativeMonomialDecomposition
import «section 5».NativeUnitGammaValues
import «section 5».NativeRVZeroPatternBases
import «section 3».RVZeroStrata
import «section 4».GammaFubiniPermutation
import «section 4».FiniteTupleBlocks

/-! # Values of relative monomial charts (Track B, exported interface)

Notation below: `𝔼 := nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind`
(nonzero RV domains), `𝔼ʳᵛ := nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind`
(RV domains with zeros), `g := nativeTorusClass B`, and
`χ J := relativeGammaEuler h00 hκ hs hr hγ kind J`
`  = GammaIteratedIntegral.integrateAll … k (indicatorFamily B J.carrier …)`.

From `InflatedRelativeMonomialDecomposition`:
```
structure RelativeMonomialChart (X : GammaGroundDefSet hc B (rawRVUnitSpace (n + r))) where
  fixedArity freeArity : ℕ;  arity_eq : fixedArity + freeArity = r
  matrix : Matrix (Fin (fixedArity + freeArity)) (Fin r) ℤ;  inverse : Matrix (Fin r) (Fin (fixedArity + freeArity)) ℤ
  matrix_mul_inverse : matrix * inverse = 1;  inverse_mul_matrix : inverse * matrix = 1
  residue : GammaGroundDefSet hc B (rawRVUnitSpace fixedArity)          -- W
  beta : Fin fixedArity → Γ;  beta_definable : ∀ i, GammaDefinableClosureAtBase B (beta i)
  residue_values : rvUnitTupleValues '' residue.carrier = {beta};  residue_nonempty : residue.carrier.Nonempty
  gamma : GammaGroundDefSet hc B (Γ^(n + freeArity))                    -- J, order (γ, η)
  source : GammaGroundDefSet hc B (rawRVUnitSpace (n + r));  source_subset : source.carrier ⊆ X.carrier
  mem_iff : ∀ z u, Fin.append z u ∈ source.carrier ↔ inflatedTop matrix u ∈ residue.carrier ∧
    Fin.append (rvUnitTupleValues z) (rvUnitTupleValues (inflatedBottom matrix u)) ∈ gamma.carrier

theorem relative_monomial_decomposition (hκ hs h00 hsmall hγsmall hΓ)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (n + r)))
    (hX : ∀ z z' u, rvUnitTupleValues z = rvUnitTupleValues z' →
      Fin.append z u ∈ X.carrier → Fin.append z' u ∈ X.carrier) :
    ∃ N, ∃ C : Fin N → RelativeMonomialChart X,
      (∀ i j, i ≠ j → Disjoint (C i).source.carrier (C j).source.carrier) ∧
      (∀ x, x ∈ X.carrier ↔ ∃ j, x ∈ (C j).source.carrier)
```
In this file:
```
theorem RelativeMonomialChart.chart_image (C) (γ) (K) (hK : ∀ η, η ∈ K.carrier ↔ Fin.append γ η ∈ C.gamma.carrier) :
    integerMonomialMap C.matrix '' {u | ∃ z, rvUnitTupleValues z = γ ∧ Fin.append z u ∈ C.source.carrier} =
      {y | (fun i => y (Fin.castAdd _ i)) ∈ C.residue.carrier ∧
        rvUnitTupleValues (fun i => y (Fin.natAdd _ i)) ∈ K.carrier}          -- (relative:monomial:chart)
theorem RelativeMonomialChart.native_value (C) :
    𝔼 C.source = 𝔼 C.residue * g ^ (n + C.freeArity) * χ C.gamma
theorem RelativeMonomialChart.fibre_mem (C) (γ) (K) (hK) (u) :
    u ∈ (C.fibre K).carrier ↔ ∃ z, rvUnitTupleValues z = γ ∧ Fin.append z u ∈ C.source.carrier
theorem RelativeMonomialChart.fibre_value (C) (K) :
    𝔼 (C.fibre K) = 𝔼 C.residue * g ^ C.freeArity * χ K
theorem relative_charts_native_value (C : Fin N → RelativeMonomialChart X) (hd) (hcov) :
    𝔼 X = ∑ j, 𝔼 (C j).residue * g ^ (n + (C j).freeArity) * χ (C j).gamma
theorem relative_charts_fibre_value (C) (hd) (hcov) (γ) (F : GammaGroundDefSet hc B (rawRVUnitSpace r))
    (hF : ∀ u, u ∈ F.carrier ↔ ∃ z, rvUnitTupleValues z = γ ∧ Fin.append z u ∈ X.carrier)
    (K : ∀ j, GammaGroundDefSet hc B (Γ^(C j).freeArity))
    (hK : ∀ j η, η ∈ (K j).carrier ↔ Fin.append γ η ∈ (C j).gamma.carrier) :
    𝔼 F = ∑ j, 𝔼 (C j).residue * g ^ (C j).freeArity * χ (K j)
def relativeGammaSlice (J : GammaGroundDefSet hc B (Γ^(n+ℓ))) (γ)
    (hγ : GammaGroundDefinable hc B (Γ^n) {γ}) : GammaGroundDefSet hc B (Γ^ℓ)
theorem relativeGammaSlice_mem : η ∈ (relativeGammaSlice J γ hγ).carrier ↔ Fin.append γ η ∈ J.carrier
def relativeGammaJoin (J : GammaGroundDefSet hc B (Γ^(n+ℓ))) : GammaGroundDefSet hc B (Γ^(n+ℓ))
theorem relativeGammaJoin_mem : join n ℓ η γ ∈ (relativeGammaJoin J).carrier ↔ Fin.append γ η ∈ J.carrier
theorem relativeGammaJoin_euler (h00 linear hκ hs hr hγ hΓ kind) (J) : χ (relativeGammaJoin J) = χ J
structure RelativeValueTerm (hc) (B) (n) where
  fixedArity freeArity : ℕ; residue : GammaGroundDefSet hc B (rawRVUnitSpace fixedArity); beta; beta_definable
  residue_values; residue_nonempty; gamma : GammaGroundDefSet hc B (Γ^(n + freeArity))
theorem inflated_relative_monomial_values (hκ hs h00 hr hγ hΓ)
    (X : GammaGroundDefSet hc B (rawRVSpace (n + r)))
    (hnz : ∀ x ∈ X.carrier, ∀ i : Fin n, x (Fin.castAdd r i) ≠ 0)
    (hX : ∀ (z z' : Fin n → RVˣ) (u : Fin r → RV), rvUnitTupleValues z = rvUnitTupleValues z' →
      Fin.append (inflatedUnitsToRV z) u ∈ X.carrier → Fin.append (inflatedUnitsToRV z') u ∈ X.carrier) :
    ∃ (ι : Type) (_ : Fintype ι) (T : ι → RelativeValueTerm hc B n), ∀ linear kind,
      𝔼ʳᵛ X = ∑ i, 𝔼 (T i).residue * g ^ (n + (T i).freeArity) * χ (T i).gamma ∧
      ∀ γ (F : GammaGroundDefSet hc B (rawRVSpace r)),
        (∀ u, u ∈ F.carrier ↔ ∃ z, rvUnitTupleValues z = γ ∧ Fin.append (inflatedUnitsToRV z) u ∈ X.carrier) →
        ∀ (K : ∀ i, GammaGroundDefSet hc B (Γ^(T i).freeArity)),
          (∀ i η, η ∈ (K i).carrier ↔ Fin.append γ η ∈ (T i).gamma.carrier) →
          𝔼ʳᵛ F = ∑ i, 𝔼 (T i).residue * g ^ (T i).freeArity * χ (K i)
```
The zero strata of the last `r` coordinates are handled with
`nativeRVZeroPatternBase`: each stratum is in definable bijection
(`inflatedUnitStratumBijection`) with a set of nonzero RV tuples obtained by
deleting its zero coordinates (`inflatedStratum`, `inflatedFibreStratum`). -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
noncomputable section
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

namespace RelativeMonomialChart
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n + r))}

/-- The product `W × J^♯` in `Fin (fixed + (n + free))` coordinates. -/
def productTarget (C : RelativeMonomialChart X) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (C.fixedArity + (n + C.freeArity))) :=
  (gammaGroundRVUnitTupleProductMap (C.residue.prod (gammaGroundRVUnitGammaPreimage C.gamma))).image

theorem productTarget_mem (C : RelativeMonomialChart X)
    (y : Fin (C.fixedArity + (n + C.freeArity)) → (CanonicalRV.RVSort M)ˣ) :
    y ∈ C.productTarget.carrier ↔
      (fun i => y (Fin.castAdd (n + C.freeArity) i)) ∈ C.residue.carrier ∧
        rvUnitTupleValues (fun i => y (Fin.natAdd C.fixedArity i)) ∈ C.gamma.carrier := by
  constructor
  · rintro ⟨⟨p, hp⟩, rfl⟩
    change (fun i => Fin.append p.1 p.2 (Fin.castAdd _ i)) ∈ C.residue.carrier ∧
      rvUnitTupleValues (fun i => Fin.append p.1 p.2 (Fin.natAdd _ i)) ∈ C.gamma.carrier
    simp only [Fin.append_left, Fin.append_right]
    exact hp
  · intro hy
    refine ⟨⟨((fun i => y (Fin.castAdd _ i)), (fun i => y (Fin.natAdd _ i))), hy⟩, ?_⟩
    change Fin.append _ _ = y
    exact Fin.append_castAdd_natAdd

/-- The coordinate permutation `(z, N u) ↦ ((N u)_fixed, z, (N u)_free)`. -/
def totalIndex (C : RelativeMonomialChart X) :
    Fin (C.fixedArity + (n + C.freeArity)) → Fin (n + (C.fixedArity + C.freeArity)) :=
  Fin.append (fun i => Fin.natAdd n (Fin.castAdd C.freeArity i))
    (Fin.append (fun j => Fin.castAdd (C.fixedArity + C.freeArity) j)
      (fun i => Fin.natAdd n (Fin.natAdd C.fixedArity i)))

/-- The integer matrix of the total chart map. -/
def totalMatrix (C : RelativeMonomialChart X) :
    Matrix (Fin (C.fixedArity + (n + C.freeArity))) (Fin (n + r)) ℤ :=
  (inflatedBlockDiag (1 : Matrix (Fin n) (Fin n) ℤ) C.matrix).submatrix C.totalIndex id

theorem totalMatrix_monomial (C : RelativeMonomialChart X) (z : Fin n → (CanonicalRV.RVSort M)ˣ)
    (u : Fin r → (CanonicalRV.RVSort M)ˣ) :
    integerMonomialMap C.totalMatrix (Fin.append z u) =
      Fin.append (inflatedTop C.matrix u) (Fin.append z (inflatedBottom C.matrix u)) := by
  rw [totalMatrix, inflatedMonomial_rows, inflatedBlockDiag_monomial, integerMonomialMap_one,
    ← inflatedTop_append_bottom C.matrix u]
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [totalIndex, Fin.append_left, Fin.append_right]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [totalIndex, Fin.append_left, Fin.append_right]
    · simp only [totalIndex, Fin.append_right]

theorem totalMatrix_mem (C : RelativeMonomialChart X) (x : C.source) :
    integerMonomialMap C.totalMatrix x.val ∈ C.productTarget.carrier := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨z, u, rfl⟩ : ∃ z u, x = Fin.append z u := ⟨_, _, (inflated_append_split x).symm⟩
  obtain ⟨hW, hJ⟩ := (C.mem_iff z u).mp hx
  rw [C.productTarget_mem, totalMatrix_monomial]
  simp only [Fin.append_left, Fin.append_right]
  refine ⟨hW, ?_⟩
  have he : (fun i => Fin.append z (inflatedBottom C.matrix u) i) =
      Fin.append z (inflatedBottom C.matrix u) := rfl
  rw [he, inflatedRVValues_append]
  exact hJ

/-- The actual definable total chart map `source → W × J^♯`. -/
def totalMap (C : RelativeMonomialChart X) : GammaGroundMap C.source C.productTarget :=
  GammaGroundMap.ofGlobal _ _ (rvUnitRectangularMonomialMap B.real C.totalMatrix)
    C.totalMatrix_mem

theorem totalMap_value (C : RelativeMonomialChart X) (x : C.source) :
    (C.totalMap x).val = integerMonomialMap C.totalMatrix x.val := rfl

theorem totalMap_bijective (C : RelativeMonomialChart X) : Function.Bijective C.totalMap := by
  constructor
  · rintro ⟨x, hx⟩ ⟨x', hx'⟩ he
    have he' := congrArg Subtype.val he
    rw [totalMap_value, totalMap_value] at he'
    obtain ⟨z, u, rfl⟩ : ∃ z u, x = Fin.append z u := ⟨_, _, (inflated_append_split x).symm⟩
    obtain ⟨z', u', rfl⟩ : ∃ z u, x' = Fin.append z u := ⟨_, _, (inflated_append_split x').symm⟩
    change integerMonomialMap C.totalMatrix (Fin.append z u) =
      integerMonomialMap C.totalMatrix (Fin.append z' u') at he'
    rw [totalMatrix_monomial, totalMatrix_monomial] at he'
    obtain ⟨h1, h2⟩ := (inflated_append_eq_iff _ _ _ _).mp he'
    obtain ⟨h3, h4⟩ := (inflated_append_eq_iff _ _ _ _).mp h2
    have hu := C.fixed_free_injective u u' h1 h4
    subst h3
    subst hu
    rfl
  · rintro ⟨y, hy⟩
    obtain ⟨hW, hJ⟩ := (C.productTarget_mem y).mp hy
    let w : Fin C.fixedArity → (CanonicalRV.RVSort M)ˣ := fun i => y (Fin.castAdd _ i)
    let z : Fin n → (CanonicalRV.RVSort M)ˣ := fun j => y (Fin.natAdd _ (Fin.castAdd _ j))
    let t : Fin C.freeArity → (CanonicalRV.RVSort M)ˣ := fun i => y (Fin.natAdd _ (Fin.natAdd n i))
    let u : Fin r → (CanonicalRV.RVSort M)ˣ := integerMonomialMap C.inverse (Fin.append w t)
    have hNu : integerMonomialMap C.matrix u = Fin.append w t := by
      rw [integerMonomialMap_comp, C.matrix_mul_inverse, integerMonomialMap_one]
    have htop : inflatedTop C.matrix u = w := by
      funext i
      rw [inflatedTop_apply, hNu]
      exact Fin.append_left _ _ i
    have hbot : inflatedBottom C.matrix u = t := by
      funext i
      rw [inflatedBottom_apply, hNu]
      exact Fin.append_right _ _ i
    have hrest : (fun i => y (Fin.natAdd C.fixedArity i)) = Fin.append z t :=
      (inflated_append_split _).symm
    have hx : Fin.append z u ∈ C.source.carrier := by
      rw [C.mem_iff, htop, hbot, ← inflatedRVValues_append, ← hrest]
      exact ⟨hW, hJ⟩
    refine ⟨⟨Fin.append z u, hx⟩, Subtype.ext ?_⟩
    rw [totalMap_value]
    change integerMonomialMap C.totalMatrix (Fin.append z u) = y
    rw [totalMatrix_monomial, htop, hbot, ← hrest]
    exact Fin.append_castAdd_natAdd

def totalBijection (C : RelativeMonomialChart X) : GammaGroundBijection C.source C.productTarget :=
  ⟨C.totalMap, C.totalMap_bijective⟩

/-- The fibre of a chart over a value tuple `γ`, given a definable slice `K`
of its value set. -/
def fibre (C : RelativeMonomialChart X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin C.freeArity))) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) r) where
  carrier := {u | inflatedTop C.matrix u ∈ C.residue.carrier ∧
    rvUnitTupleValues (inflatedBottom C.matrix u) ∈ K.carrier}
  definable := by
    apply ((C.residue.definable.preimage (rvUnitRectangularMonomialMap B.real
      (C.matrix.submatrix (Fin.castAdd C.freeArity) id))).inter
      ((gammaGroundRVUnitGammaPreimage K).definable.preimage (rvUnitRectangularMonomialMap B.real
        (C.matrix.submatrix (Fin.natAdd C.fixedArity) id)))).congr
    intro u
    rfl

theorem fibre_mem (C : RelativeMonomialChart X) (γ : Fin n → Values.Gamma (M := M))
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin C.freeArity)))
    (hK : ∀ η, η ∈ K.carrier ↔ Fin.append γ η ∈ C.gamma.carrier)
    (u : Fin r → (CanonicalRV.RVSort M)ˣ) :
    u ∈ (C.fibre K).carrier ↔
      ∃ z : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitTupleValues z = γ ∧
        Fin.append z u ∈ C.source.carrier := by
  constructor
  · rintro ⟨hW, hk⟩
    obtain ⟨z, hz⟩ := rvUnitTupleValues_surjective n γ
    refine ⟨z, hz, (C.mem_iff z u).mpr ⟨hW, ?_⟩⟩
    rw [hz]
    exact (hK _).mp hk
  · rintro ⟨z, hz, hx⟩
    obtain ⟨hW, hJ⟩ := (C.mem_iff z u).mp hx
    rw [hz] at hJ
    exact ⟨hW, (hK _).mpr hJ⟩

/-- The product `W × K^♯` in `Fin (fixed + free)` coordinates. -/
def fibreTarget (C : RelativeMonomialChart X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin C.freeArity))) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (C.fixedArity + C.freeArity)) :=
  (gammaGroundRVUnitTupleProductMap (C.residue.prod (gammaGroundRVUnitGammaPreimage K))).image

theorem fibreTarget_mem (C : RelativeMonomialChart X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin C.freeArity)))
    (y : Fin (C.fixedArity + C.freeArity) → (CanonicalRV.RVSort M)ˣ) :
    y ∈ (C.fibreTarget K).carrier ↔
      (fun i => y (Fin.castAdd C.freeArity i)) ∈ C.residue.carrier ∧
        rvUnitTupleValues (fun i => y (Fin.natAdd C.fixedArity i)) ∈ K.carrier := by
  constructor
  · rintro ⟨⟨p, hp⟩, rfl⟩
    change (fun i => Fin.append p.1 p.2 (Fin.castAdd _ i)) ∈ C.residue.carrier ∧
      rvUnitTupleValues (fun i => Fin.append p.1 p.2 (Fin.natAdd _ i)) ∈ K.carrier
    simp only [Fin.append_left, Fin.append_right]
    exact hp
  · intro hy
    refine ⟨⟨((fun i => y (Fin.castAdd _ i)), (fun i => y (Fin.natAdd _ i))), hy⟩, ?_⟩
    change Fin.append _ _ = y
    exact Fin.append_castAdd_natAdd

def fibreMap (C : RelativeMonomialChart X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin C.freeArity))) :
    GammaGroundMap (C.fibre K) (C.fibreTarget K) :=
  GammaGroundMap.ofGlobal _ _ (rvUnitRectangularMonomialMap B.real C.matrix) (by
    rintro ⟨u, hW, hk⟩
    rw [C.fibreTarget_mem]
    exact ⟨hW, hk⟩)

theorem fibreMap_bijective (C : RelativeMonomialChart X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin C.freeArity))) :
    Function.Bijective (C.fibreMap K) := by
  constructor
  · rintro ⟨u, hu⟩ ⟨u', hu'⟩ he
    have he' : integerMonomialMap C.matrix u = integerMonomialMap C.matrix u' :=
      congrArg Subtype.val he
    exact Subtype.ext (inflatedMonomial_injective C.matrix C.inverse C.inverse_mul_matrix he')
  · rintro ⟨y, hy⟩
    obtain ⟨hW, hk⟩ := (C.fibreTarget_mem K y).mp hy
    let u : Fin r → (CanonicalRV.RVSort M)ˣ := integerMonomialMap C.inverse y
    have hNu : integerMonomialMap C.matrix u = y := by
      rw [integerMonomialMap_comp, C.matrix_mul_inverse, integerMonomialMap_one]
    refine ⟨⟨u, ?_, ?_⟩, Subtype.ext hNu⟩
    · change (fun i => integerMonomialMap C.matrix u (Fin.castAdd _ i)) ∈ C.residue.carrier
      rw [hNu]
      exact hW
    · change rvUnitTupleValues (fun i => integerMonomialMap C.matrix u (Fin.natAdd _ i)) ∈ K.carrier
      rw [hNu]
      exact hk

def fibreBijection (C : RelativeMonomialChart X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin C.freeArity))) :
    GammaGroundBijection (C.fibre K) (C.fibreTarget K) :=
  ⟨C.fibreMap K, C.fibreMap_bijective K⟩

/-- The literal chart identity `h_N(U_γ) = W × (J_γ)^♯`, where
`U_γ = {u | ∃ z, vrv z = γ ∧ (z,u) ∈ source}` and `K = J_γ`. -/
theorem chart_image (C : RelativeMonomialChart X) (γ : Fin n → Values.Gamma (M := M))
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin C.freeArity)))
    (hK : ∀ η, η ∈ K.carrier ↔ Fin.append γ η ∈ C.gamma.carrier) :
    integerMonomialMap C.matrix ''
        {u | ∃ z : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitTupleValues z = γ ∧
          Fin.append z u ∈ C.source.carrier} =
      {y | (fun i => y (Fin.castAdd C.freeArity i)) ∈ C.residue.carrier ∧
        rvUnitTupleValues (fun i => y (Fin.natAdd C.fixedArity i)) ∈ K.carrier} := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ((C.fibre_mem γ K hK u).mpr hu)
  · intro hy
    obtain ⟨⟨u, hu⟩, hyu⟩ := (C.fibreMap_bijective K).2 ⟨y, (C.fibreTarget_mem K y).mpr hy⟩
    refine ⟨u, (C.fibre_mem γ K hK u).mp hu, ?_⟩
    exact congrArg Subtype.val hyu

end RelativeMonomialChart

section Values
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)

/-- `χ(J)`: the Gamma Euler integral of an original-ground Gamma set. -/
abbrev relativeGammaEuler {k : ℕ} (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin k))) :
    RESDimensionFreeReduction.Ring B :=
  (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ kind k
    (GammaIndicators.indicatorFamily B J.carrier (Section3GammaChartBridge.chart J).support_definable) :
      RESDimensionFreeReduction.Ring B)

namespace RelativeMonomialChart
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n + r))}

/-- Total chart value: `[source] = [W] g^(n+ℓ) χ(J)`. -/
theorem native_value (C : RelativeMonomialChart X) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind C.source =
      nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind C.residue *
        nativeTorusClass B ^ (n + C.freeArity) *
          relativeGammaEuler h00 hκ hs hr hγ kind C.gamma := by
  rw [nativeUnitRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _ C.totalBijection,
    productTarget, nativeUnitRVSetValue_product, nativeUnitRVSetValue_gamma]
  ring

/-- Fibre chart value: `[fibre] = [W] g^ℓ χ(K)`. -/
theorem fibre_value (C : RelativeMonomialChart X)
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin C.freeArity))) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (C.fibre K) =
      nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind C.residue *
        nativeTorusClass B ^ C.freeArity * relativeGammaEuler h00 hκ hs hr hγ kind K := by
  rw [nativeUnitRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _ (C.fibreBijection K),
    fibreTarget, nativeUnitRVSetValue_product, nativeUnitRVSetValue_gamma]
  ring

end RelativeMonomialChart

variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n + r))}

/-- Total value of a chart partition. -/
theorem relative_charts_native_value {N : ℕ} (C : Fin N → RelativeMonomialChart X)
    (hd : ∀ i j, i ≠ j → Disjoint (C i).source.carrier (C j).source.carrier)
    (hcov : ∀ x, x ∈ X.carrier ↔ ∃ j, x ∈ (C j).source.carrier) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X =
      ∑ j, nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (C j).residue *
        nativeTorusClass B ^ (n + (C j).freeArity) *
          relativeGammaEuler h00 hκ hs hr hγ kind (C j).gamma := by
  rw [nativeUnitRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind X
    (fun j => (C j).source) hd hcov]
  exact Finset.sum_congr rfl (fun j _ => (C j).native_value h00 linear hκ hs hr hγ hΓ kind)

/-- Fibre value of a chart partition at a value tuple `γ`. -/
theorem relative_charts_fibre_value {N : ℕ} (C : Fin N → RelativeMonomialChart X)
    (hd : ∀ i j, i ≠ j → Disjoint (C i).source.carrier (C j).source.carrier)
    (hcov : ∀ x, x ∈ X.carrier ↔ ∃ j, x ∈ (C j).source.carrier)
    (γ : Fin n → Values.Gamma (M := M)) (F : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) r))
    (hF : ∀ u, u ∈ F.carrier ↔ ∃ z : Fin n → (CanonicalRV.RVSort M)ˣ,
      rvUnitTupleValues z = γ ∧ Fin.append z u ∈ X.carrier)
    (K : ∀ j, GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (C j).freeArity)))
    (hK : ∀ j η, η ∈ (K j).carrier ↔ Fin.append γ η ∈ (C j).gamma.carrier) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind F =
      ∑ j, nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (C j).residue *
        nativeTorusClass B ^ (C j).freeArity * relativeGammaEuler h00 hκ hs hr hγ kind (K j) := by
  have hdisj : ∀ i j, i ≠ j → Disjoint ((C i).fibre (K i)).carrier ((C j).fibre (K j)).carrier := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro u hi hj
    obtain ⟨z, hz, hzi⟩ := ((C i).fibre_mem γ (K i) (hK i) u).mp hi
    obtain ⟨z', hz', hzj⟩ := ((C j).fibre_mem γ (K j) (hK j) u).mp hj
    have hzj' := ((C j).source_invariant z' z u (hz'.trans hz.symm)).mp hzj
    exact Set.disjoint_left.mp (hd i j hij) hzi hzj'
  have hcov' : ∀ u, u ∈ F.carrier ↔ ∃ j, u ∈ ((C j).fibre (K j)).carrier := by
    intro u
    rw [hF]
    constructor
    · rintro ⟨z, hz, hx⟩
      obtain ⟨j, hj⟩ := (hcov _).mp hx
      exact ⟨j, ((C j).fibre_mem γ (K j) (hK j) u).mpr ⟨z, hz, hj⟩⟩
    · rintro ⟨j, hj⟩
      obtain ⟨z, hz, hx⟩ := ((C j).fibre_mem γ (K j) (hK j) u).mp hj
      exact ⟨z, hz, (C j).source_subset hx⟩
  rw [nativeUnitRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind F
    (fun j => (C j).fibre (K j)) hdisj hcov']
  exact Finset.sum_congr rfl (fun j _ => (C j).fibre_value h00 linear hκ hs hr hγ hΓ kind (K j))

end Values

section Slices

/-- The slice `J_γ = {η | (γ, η) ∈ J}` of an original-ground value set at a
definable value tuple `γ`. -/
def relativeGammaSlice {ℓ : ℕ}
    (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + ℓ))))
    (γ : Fin n → Values.Gamma (M := M))
    (hγ : GammaGroundDefinable hc B ((volumeGammaSpace hc).power (Fin n)) {γ}) :
    GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin ℓ)) where
  carrier := {η | Fin.append γ η ∈ J.carrier}
  definable := by
    let P := (volumeGammaSpace hc).power (Fin n)
    let Q := (volumeGammaSpace hc).power (Fin ℓ)
    let app : Map (DefSet.univ (P.prod Q) B.real)
        (DefSet.univ ((volumeGammaSpace hc).power (Fin (n + ℓ))) B.real) :=
      (gammaAppendMap (DefSet.univ P B.real) (DefSet.univ Q B.real)).comp
        ((universalProductFst P Q B.real).pair (universalProductSnd P Q B.real))
    have hJ := J.definable.preimage app
    apply ((hJ.inter (hγ.preimage (universalProductFst P Q B.real))).image
      (universalProductSnd P Q B.real)).congr
    intro η
    constructor
    · rintro ⟨w, ⟨hw, hwγ⟩, hwη⟩
      change w.1 = γ at hwγ
      change w.2 = η at hwη
      change Fin.append w.1 w.2 ∈ J.carrier at hw
      rw [hwγ, hwη] at hw
      exact hw
    · intro hη
      exact ⟨(γ, η), ⟨hη, rfl⟩, rfl⟩

theorem relativeGammaSlice_mem {ℓ : ℕ}
    (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + ℓ))))
    (γ : Fin n → Values.Gamma (M := M))
    (hγ : GammaGroundDefinable hc B ((volumeGammaSpace hc).power (Fin n)) {γ})
    (η : Fin ℓ → Values.Gamma (M := M)) :
    η ∈ (relativeGammaSlice J γ hγ).carrier ↔ Fin.append γ η ∈ J.carrier := Iff.rfl

end Slices

section JoinOrder
open DiamondIntegral.Section4.FiniteTupleBlocks

theorem relativeJoinIndex_injective (n ℓ : ℕ) :
    Function.Injective (Fin.append (tailIndex n ℓ) (headIndex n ℓ)) := by
  have hdis : ∀ i j, tailIndex n ℓ i ≠ headIndex n ℓ j := by
    intro i j he
    have h1 := join_tail n ℓ (fun _ => true) (fun _ => false) i
    have h2 := join_head n ℓ (fun _ => true) (fun _ => false) j
    rw [he, h2] at h1
    exact Bool.noConfusion h1
  intro a b hab
  revert hab
  refine Fin.addCases (fun i => ?_) (fun j => ?_) a <;>
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) b <;>
    simp only [Fin.append_left, Fin.append_right] <;> intro hab
  · rw [tailIndex_injective n ℓ hab]
  · exact absurd hab (hdis i j')
  · exact absurd hab.symm (hdis i' j)
  · rw [headIndex_injective n ℓ hab]

/-- The coordinate permutation from the Section 4 block order
(integrated coordinates first) to the `Fin.append γ η` order. -/
def relativeJoinEquiv (n ℓ : ℕ) : Fin (n + ℓ) ≃ Fin (n + ℓ) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (relativeJoinIndex_injective n ℓ))

theorem relativeJoinEquiv_comp {α : Type} (n ℓ : ℕ) (w : Fin (n + ℓ) → α) :
    (fun i => w (relativeJoinEquiv n ℓ i)) =
      Fin.append (fun i => w (tailIndex n ℓ i)) (fun i => w (headIndex n ℓ i)) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · change w (Fin.append (tailIndex n ℓ) (headIndex n ℓ) (Fin.castAdd ℓ i)) = _
    rw [Fin.append_left, Fin.append_left]
  · change w (Fin.append (tailIndex n ℓ) (headIndex n ℓ) (Fin.natAdd n i)) = _
    rw [Fin.append_right, Fin.append_right]

/-- A value set `J ⊆ Γ^n × Γ^ℓ` (in `Fin.append γ η` order) rewritten in the
Section 4 block order `join n ℓ η γ`, integrated coordinates first. -/
def relativeGammaJoin {ℓ : ℕ}
    (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + ℓ)))) :
    GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + ℓ))) where
  carrier := {w | (fun i => w (relativeJoinEquiv n ℓ i)) ∈ J.carrier}
  definable := J.definable.preimage
    (universalPowerProjection (volumeGammaSpace hc) B.real (relativeJoinEquiv n ℓ))

theorem relativeGammaJoin_mem {ℓ : ℕ}
    (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + ℓ))))
    (η : Fin ℓ → Values.Gamma (M := M)) (γ : Fin n → Values.Gamma (M := M)) :
    join n ℓ η γ ∈ (relativeGammaJoin J).carrier ↔ Fin.append γ η ∈ J.carrier := by
  change (fun i => join n ℓ η γ (relativeJoinEquiv n ℓ i)) ∈ J.carrier ↔ _
  rw [relativeJoinEquiv_comp]
  have h1 : (fun i => join n ℓ η γ (tailIndex n ℓ i)) = γ := funext (join_tail n ℓ η γ)
  have h2 : (fun i => join n ℓ η γ (headIndex n ℓ i)) = η := funext (join_head n ℓ η γ)
  rw [h1, h2]

/-- The block-order rewriting does not change the Gamma Euler integral. -/
theorem relativeGammaJoin_euler (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind) {ℓ : ℕ}
    (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + ℓ)))) :
    relativeGammaEuler h00 hκ hs hr hγ kind (relativeGammaJoin J) =
      relativeGammaEuler h00 hκ hs hr hγ kind J := by
  have hpull : GammaCoordinatePullback.pullback B (relativeJoinEquiv n ℓ)
      (GammaIndicators.indicatorFamily B J.carrier (Section3GammaChartBridge.chart J).support_definable) =
      GammaIndicators.indicatorFamily B (relativeGammaJoin J).carrier
        (Section3GammaChartBridge.chart (relativeGammaJoin J)).support_definable := by
    apply Subtype.ext
    rfl
  unfold relativeGammaEuler
  rw [← hpull, GammaFubiniPermutation.integrateAll_equiv h00 hκ hs B hr hγ kind linear hΓ]

end JoinOrder

section ZeroStrata

/-- The value of an RV unit is its `vrv` (bridge to `vrv`-phrased families). -/
theorem inflatedRVUnitValue_val (t : (CanonicalRV.RVSort M)ˣ) :
    (rvUnitValueHom t).val = Values.vrv (t : CanonicalRV.RVSort M) := rfl

theorem inflatedRV_ne_zero_iff (t : CanonicalRV.RVSort M) : t ≠ 0 ↔ t.val ≠ iRVZero := by
  rw [← RVOperations.zero_val, Ne, Ne, Subtype.ext_iff]

/-- Deleting the coordinates outside `e`: the nonzero RV tuples `y` such
that some point of `A` restricts along `e` to `y`. -/
def inflatedUnitStratum {p q : ℕ} (A : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (e : Fin q → Fin p) : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) q) where
  carrier := {y | ∃ x ∈ A.carrier, (fun i => x (e i)) = (fun i => (y i : CanonicalRV.RVSort M))}
  definable := by
    apply ((A.definable.image (rvSelectCoordinates e (DefSet.univ (rawRVSpace (M := M) p) B.real))).preimage
      (rvUnitToRVMap (DefSet.univ (rawRVUnitSpace (M := M) q) B.real))).congr
    intro y
    exact Iff.rfl

/-- A set of RV tuples, nonzero exactly at the coordinates `e`, is in
definable bijection with its nonzero presentation. -/
def inflatedUnitStratumBijection {p q : ℕ} (A : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (e : Fin q → Fin p) (hnz : ∀ x ∈ A.carrier, ∀ i, x (e i) ≠ 0)
    (hz : ∀ x ∈ A.carrier, ∀ j, j ∉ Set.range e → x j = 0) :
    GammaGroundBijection A (gammaGroundRVUnitToRVMap (inflatedUnitStratum A e)).image where
  map := GammaGroundMap.ofGlobal _ _ (rvSelectCoordinates e (DefSet.univ (rawRVSpace (M := M) p) B.real))
    (by
      rintro ⟨x, hx⟩
      let y : Fin q → (CanonicalRV.RVSort M)ˣ := fun i => Units.mk0 (x (e i)) (hnz x hx i)
      have hy : y ∈ (inflatedUnitStratum A e).carrier := ⟨x, hx, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩)
  bijective := by
    constructor
    · rintro ⟨x, hx⟩ ⟨x', hx'⟩ he
      have he' : (fun i => x (e i)) = (fun i => x' (e i)) := congrArg Subtype.val he
      apply Subtype.ext
      funext j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        exact congrFun he' i
      · change x j = x' j
        rw [hz x hx j hj, hz x' hx' j hj]
    · rintro ⟨t, ⟨y, x, hx, hxy⟩, rfl⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

section StratumValues
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)

theorem inflatedUnitStratum_value {p q : ℕ} (A : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (e : Fin q → Fin p) (hnz : ∀ x ∈ A.carrier, ∀ i, x (e i) ≠ 0)
    (hz : ∀ x ∈ A.carrier, ∀ j, j ∉ Set.range e → x j = 0) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (inflatedUnitStratum A e) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind A :=
  (nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (inflatedUnitStratumBijection A e hnz hz)).symm

end StratumValues

/-- Enumeration of the nonzero coordinates of a zero pattern. -/
def inflatedPatternIndex {r : ℕ} (I : Finset (Fin r)) : Fin I.card → Fin r :=
  I.orderEmbOfFin rfl

/-- The retained coordinates of a zero stratum: all of `z`, then the
nonzero coordinates of `u`. -/
def inflatedStratumIndex (n : ℕ) {r : ℕ} (I : Finset (Fin r)) : Fin (n + I.card) → Fin (n + r) :=
  Fin.append (Fin.castAdd r) (fun i => Fin.natAdd n (inflatedPatternIndex I i))

theorem inflatedPatternIndex_mem {r : ℕ} (I : Finset (Fin r)) (i : Fin I.card) :
    inflatedPatternIndex I i ∈ I :=
  I.orderEmbOfFin_mem rfl i

theorem inflatedPatternIndex_cover {r : ℕ} (I : Finset (Fin r)) (k : Fin r) (hk : k ∈ I) :
    ∃ i, inflatedPatternIndex I i = k := by
  have h : k ∈ Set.range (I.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hk
  exact h

/-- The zero stratum `I` of `X ⊆ RV^(n+r)`, as nonzero tuples in
`(RV^×)^(n + |I|)`. -/
def inflatedStratum (X : GammaGroundDefSet hc B (rawRVSpace (M := M) (n + r))) (I : Finset (Fin r)) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n + I.card)) :=
  inflatedUnitStratum (nativeRVZeroPatternBase X (Fin.natAdd n) I) (inflatedStratumIndex n I)

/-- The zero stratum `I` of a fibre `F ⊆ RV^r`, as nonzero tuples. -/
def inflatedFibreStratum (F : GammaGroundDefSet hc B (rawRVSpace (M := M) r)) (I : Finset (Fin r)) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) I.card) :=
  inflatedUnitStratum (nativeRVZeroPatternBase F id I) (inflatedPatternIndex I)

theorem inflatedPattern_iff {p d : ℕ} (A : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (j : Fin d → Fin p) (I : Finset (Fin d)) (x : Fin p → CanonicalRV.RVSort M) :
    x ∈ (nativeRVZeroPatternBase A j I).carrier ↔ x ∈ A.carrier ∧ ∀ i, i ∈ I ↔ x (j i) ≠ 0 := by
  rw [nativeRVZeroPatternBase_mem]
  simp only [nativeRVZeroPattern, rvValues, inflatedRV_ne_zero_iff]

/-- Units included as RV elements. -/
abbrev inflatedUnitsToRV {k : ℕ} (z : Fin k → (CanonicalRV.RVSort M)ˣ) : Fin k → CanonicalRV.RVSort M :=
  fun i => (z i : CanonicalRV.RVSort M)

theorem inflatedStratum_restrict {I : Finset (Fin r)} {x : Fin (n + r) → CanonicalRV.RVSort M}
    {z : Fin n → (CanonicalRV.RVSort M)ˣ} {w : Fin I.card → (CanonicalRV.RVSort M)ˣ}
    (hxw : (fun i => x (inflatedStratumIndex n I i)) = inflatedUnitsToRV (Fin.append z w)) :
    x = Fin.append (inflatedUnitsToRV z) (fun k => x (Fin.natAdd n k)) ∧
      ∀ i, x (Fin.natAdd n (inflatedPatternIndex I i)) = (w i : CanonicalRV.RVSort M) := by
  constructor
  · funext j
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · have h := congrFun hxw (Fin.castAdd I.card i)
      simp only [inflatedStratumIndex, Fin.append_left, inflatedUnitsToRV] at h
      rw [Fin.append_left]
      exact h
    · rw [Fin.append_right]
  · intro i
    have h := congrFun hxw (Fin.natAdd n i)
    simpa only [inflatedStratumIndex, Fin.append_right, inflatedUnitsToRV] using h

theorem inflatedStratum_conditions (X : GammaGroundDefSet hc B (rawRVSpace (M := M) (n + r)))
    (hnz : ∀ x ∈ X.carrier, ∀ i : Fin n, x (Fin.castAdd r i) ≠ 0) (I : Finset (Fin r)) :
    (∀ x ∈ (nativeRVZeroPatternBase X (Fin.natAdd n) I).carrier, ∀ i, x (inflatedStratumIndex n I i) ≠ 0) ∧
      (∀ x ∈ (nativeRVZeroPatternBase X (Fin.natAdd n) I).carrier, ∀ j,
        j ∉ Set.range (inflatedStratumIndex n I) → x j = 0) := by
  constructor
  · intro x hx i
    obtain ⟨hX, hp⟩ := (inflatedPattern_iff X _ I x).mp hx
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [inflatedStratumIndex, Fin.append_left]
      exact hnz x hX i
    · simp only [inflatedStratumIndex, Fin.append_right]
      exact (hp _).mp (inflatedPatternIndex_mem I i)
  · intro x hx j hj
    obtain ⟨_, hp⟩ := (inflatedPattern_iff X _ I x).mp hx
    revert hj
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · intro hj
      exact absurd ⟨Fin.castAdd I.card i, by simp only [inflatedStratumIndex, Fin.append_left]⟩ hj
    · intro hj
      by_contra hne
      obtain ⟨i, hi⟩ := inflatedPatternIndex_cover I k ((hp k).mpr hne)
      exact hj ⟨Fin.natAdd n i, by simp only [inflatedStratumIndex, Fin.append_right, hi]⟩

theorem inflatedFibreStratum_conditions (F : GammaGroundDefSet hc B (rawRVSpace (M := M) r))
    (I : Finset (Fin r)) :
    (∀ u ∈ (nativeRVZeroPatternBase F id I).carrier, ∀ i, u (inflatedPatternIndex I i) ≠ 0) ∧
      (∀ u ∈ (nativeRVZeroPatternBase F id I).carrier, ∀ k,
        k ∉ Set.range (inflatedPatternIndex I) → u k = 0) := by
  constructor
  · intro u hu i
    exact ((inflatedPattern_iff F id I u).mp hu).2 _ |>.mp (inflatedPatternIndex_mem I i)
  · intro u hu k hk
    by_contra hne
    obtain ⟨i, hi⟩ := inflatedPatternIndex_cover I k
      ((((inflatedPattern_iff F id I u).mp hu).2 k).mpr hne)
    exact hk ⟨i, hi⟩

theorem inflatedStratum_invariant (X : GammaGroundDefSet hc B (rawRVSpace (M := M) (n + r)))
    (hX : ∀ (z z' : Fin n → (CanonicalRV.RVSort M)ˣ) (u : Fin r → CanonicalRV.RVSort M),
      rvUnitTupleValues z = rvUnitTupleValues z' →
      Fin.append (inflatedUnitsToRV z) u ∈ X.carrier → Fin.append (inflatedUnitsToRV z') u ∈ X.carrier)
    (I : Finset (Fin r)) (z z' : Fin n → (CanonicalRV.RVSort M)ˣ)
    (w : Fin I.card → (CanonicalRV.RVSort M)ˣ) (hzz : rvUnitTupleValues z = rvUnitTupleValues z')
    (hw : Fin.append z w ∈ (inflatedStratum X I).carrier) :
    Fin.append z' w ∈ (inflatedStratum X I).carrier := by
  obtain ⟨x, hx, hxw⟩ := hw
  obtain ⟨hsplit, hval⟩ := inflatedStratum_restrict hxw
  obtain ⟨hxX, hp⟩ := (inflatedPattern_iff X _ I x).mp hx
  let u : Fin r → CanonicalRV.RVSort M := fun k => x (Fin.natAdd n k)
  have hx' : Fin.append (inflatedUnitsToRV z') u ∈ X.carrier := hX z z' u hzz (hsplit ▸ hxX)
  refine ⟨Fin.append (inflatedUnitsToRV z') u, (inflatedPattern_iff X _ I _).mpr ⟨hx', ?_⟩, ?_⟩
  · intro i
    rw [Fin.append_right]
    exact hp i
  · funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [inflatedStratumIndex, Fin.append_left, inflatedUnitsToRV]
    · simp only [inflatedStratumIndex, Fin.append_right, u]
      exact hval i

theorem inflatedFibreStratum_mem (X : GammaGroundDefSet hc B (rawRVSpace (M := M) (n + r)))
    (γ : Fin n → Values.Gamma (M := M)) (F : GammaGroundDefSet hc B (rawRVSpace (M := M) r))
    (hF : ∀ u, u ∈ F.carrier ↔ ∃ z : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitTupleValues z = γ ∧
      Fin.append (inflatedUnitsToRV z) u ∈ X.carrier)
    (I : Finset (Fin r)) (w : Fin I.card → (CanonicalRV.RVSort M)ˣ) :
    w ∈ (inflatedFibreStratum F I).carrier ↔
      ∃ z : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitTupleValues z = γ ∧
        Fin.append z w ∈ (inflatedStratum X I).carrier := by
  constructor
  · rintro ⟨u, hu, huw⟩
    obtain ⟨huF, hp⟩ := (inflatedPattern_iff F id I u).mp hu
    obtain ⟨z, hz, hzu⟩ := (hF u).mp huF
    refine ⟨z, hz, Fin.append (inflatedUnitsToRV z) u, (inflatedPattern_iff X _ I _).mpr ⟨hzu, ?_⟩, ?_⟩
    · intro i
      rw [Fin.append_right]
      exact hp i
    · funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [inflatedStratumIndex, Fin.append_left, inflatedUnitsToRV]
      · simp only [inflatedStratumIndex, Fin.append_right]
        exact congrFun huw i
  · rintro ⟨z, hz, x, hx, hxw⟩
    obtain ⟨hsplit, hval⟩ := inflatedStratum_restrict hxw
    obtain ⟨hxX, hp⟩ := (inflatedPattern_iff X _ I x).mp hx
    let u : Fin r → CanonicalRV.RVSort M := fun k => x (Fin.natAdd n k)
    refine ⟨u, (inflatedPattern_iff F id I u).mpr ⟨(hF u).mpr ⟨z, hz, hsplit ▸ hxX⟩, hp⟩, ?_⟩
    funext i
    exact hval i

end ZeroStrata

/-- One contribution `[W] g^ℓ χ(J)` of a relative monomial decomposition. -/
structure RelativeValueTerm (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    (n : ℕ) where
  fixedArity : ℕ
  freeArity : ℕ
  residue : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) fixedArity)
  beta : Fin fixedArity → Values.Gamma (M := M)
  beta_definable : ∀ i, GammaDefinableClosureAtBase B (beta i)
  residue_values : rvUnitTupleValues '' residue.carrier = {beta}
  residue_nonempty : residue.carrier.Nonempty
  gamma : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + freeArity)))

def RelativeMonomialChart.toTerm {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n + r))}
    (C : RelativeMonomialChart X) : RelativeValueTerm hc B n :=
  ⟨C.fixedArity, C.freeArity, C.residue, C.beta, C.beta_definable, C.residue_values,
    C.residue_nonempty, C.gamma⟩

/-- Main export: relative monomial values of an inflated RV family, zero
strata included. The same finite decomposition serves both Euler kinds and
every value tuple `γ`. -/
theorem inflated_relative_monomial_values {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) (n + r)))
    (hnz : ∀ x ∈ X.carrier, ∀ i : Fin n, x (Fin.castAdd r i) ≠ 0)
    (hX : ∀ (z z' : Fin n → (CanonicalRV.RVSort M)ˣ) (u : Fin r → CanonicalRV.RVSort M),
      rvUnitTupleValues z = rvUnitTupleValues z' →
      Fin.append (inflatedUnitsToRV z) u ∈ X.carrier → Fin.append (inflatedUnitsToRV z') u ∈ X.carrier) :
    ∃ (ι : Type) (_ : Fintype ι) (T : ι → RelativeValueTerm hc B n),
      ∀ (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) (kind : EulerKind),
        nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X =
          ∑ i, nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (T i).residue *
            nativeTorusClass B ^ (n + (T i).freeArity) *
              relativeGammaEuler h00 hκ hs hr hγ kind (T i).gamma ∧
        ∀ (γ : Fin n → Values.Gamma (M := M)) (F : GammaGroundDefSet hc B (rawRVSpace (M := M) r)),
          (∀ u, u ∈ F.carrier ↔ ∃ z : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitTupleValues z = γ ∧
            Fin.append (inflatedUnitsToRV z) u ∈ X.carrier) →
          ∀ (K : ∀ i, GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (T i).freeArity))),
            (∀ i η, η ∈ (K i).carrier ↔ Fin.append γ η ∈ (T i).gamma.carrier) →
            nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind F =
              ∑ i, nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (T i).residue *
                nativeTorusClass B ^ (T i).freeArity *
                  relativeGammaEuler h00 hκ hs hr hγ kind (K i) := by
  choose N C hd hcov using fun I : Finset (Fin r) =>
    relative_monomial_decomposition hκ hs h00 hr hγ hΓ (inflatedStratum X I)
      (fun z z' w hzz hw => inflatedStratum_invariant X hX I z z' w hzz hw)
  refine ⟨(I : Finset (Fin r)) × Fin (N I), inferInstance, fun i => (C i.1 i.2).toTerm, ?_⟩
  intro linear kind
  constructor
  · rw [nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind X
      (fun I => nativeRVZeroPatternBase X (Fin.natAdd n) I)
      (fun I J hne => nativeRVZeroPatternBase_disjoint X _ I J hne)
      (nativeRVZeroPatternBase_cover X _), Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro I _
    obtain ⟨h1, h2⟩ := inflatedStratum_conditions X hnz I
    rw [← inflatedUnitStratum_value h00 linear hκ hs hr hγ hΓ kind _ _ h1 h2]
    exact relative_charts_native_value h00 linear hκ hs hr hγ hΓ kind (C I) (hd I) (hcov I)
  · intro γ F hF K hK
    rw [nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind F
      (fun I => nativeRVZeroPatternBase F id I)
      (fun I J hne => nativeRVZeroPatternBase_disjoint F _ I J hne)
      (nativeRVZeroPatternBase_cover F _), Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro I _
    obtain ⟨h1, h2⟩ := inflatedFibreStratum_conditions F I
    rw [← inflatedUnitStratum_value h00 linear hκ hs hr hγ hΓ kind _ _ h1 h2]
    exact relative_charts_fibre_value h00 linear hκ hs hr hγ hΓ kind (C I) (hd I) (hcov I) γ
      (inflatedFibreStratum F I) (inflatedFibreStratum_mem X γ F hF I)
      (fun c => K ⟨I, c⟩) (fun c => hK ⟨I, c⟩)

end DiamondIntegral.Section5
