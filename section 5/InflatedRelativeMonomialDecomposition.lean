import «section 5».InflatedIntegerBlockReduction
import «section 5».MonomialMatrixForm
import «section 3».RVResidueFullFibreCoordinates
import «section 3».RVUnitRectangularMonomials
import «section 3».RVUnitGammaMaps
import «section 4».GammaNamesSubgroup

/-! Relative monomial decomposition (claim (relative:monomial:chart) in the
proof of the inflated-family Fubini theorem).

Let `X ⊆ (RV^×)^n × (RV^×)^r` be original-ground definable, with coordinates
`(z,u)`, and suppose that `X` depends on `z` only through `vrv z`. Then `X`
has a finite disjoint definable partition into chart sources. Each chart has
an integer matrix `N` with two-sided integer inverse acting on `u` alone, a
fixed nonempty residue set `W` with one original-ground value tuple, and an
original-ground definable value set `J ⊆ Γ^n × Γ^ℓ`, such that

  `(z,u) ∈ source ↔ (N u)_fixed ∈ W ∧ (vrv z, vrv (N u)_free) ∈ J`.

The proof applies `monomial_decomposition_5_12` to `X`, Smith-reduces the
`z` block of each piece, uses algebraic closedness of the residue field for
the divisibility of residue units, and extends the primitive rows. The value
set `J` is the value image of the source, so no angular representative is
retained as a parameter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
noncomputable section
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Residue units are divisible: the residue field is algebraically closed. -/
theorem inflatedRVResidue_divisible (d : ℤ) (hd : d ≠ 0) (g : (CanonicalRV.RVSort M)ˣ)
    (hg : g ∈ (rvUnitValueHom (M := M)).ker) :
    ∃ x ∈ (rvUnitValueHom (M := M)).ker, x ^ d = g := by
  have : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  have : IsAlgClosed (RVResidueField M) :=
    ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  obtain ⟨z, hz⟩ := exists_residueUnitToRV_of_value_one g (MonoidHom.mem_ker.mp hg)
  have hn : 0 < d.natAbs := Int.natAbs_pos.mpr hd
  obtain ⟨w0, hw0⟩ := IsAlgClosed.exists_pow_nat_eq ((z : RVResidueField M)) hn
  have hw0ne : w0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.pos_iff_ne_zero.mp hn)] at hw0
    exact Units.ne_zero z hw0.symm
  let w : (RVResidueField M)ˣ := Units.mk0 w0 hw0ne
  have hw : w ^ d.natAbs = z := Units.ext (by simpa only [Units.val_pow_eq_pow_val, w,
    Units.val_mk0] using hw0)
  have hwd : ∃ x : (RVResidueField M)ˣ, x ^ d = z := by
    rcases Int.natAbs_eq d with h | h
    · refine ⟨w, ?_⟩
      rw [h, zpow_natCast, hw]
    · refine ⟨w⁻¹, ?_⟩
      rw [h, inv_zpow', neg_neg, zpow_natCast, hw]
  obtain ⟨x, hx⟩ := hwd
  refine ⟨residueUnitToRV x, MonoidHom.mem_ker.mpr (residueUnitToRV_value_one x), ?_⟩
  rw [← map_zpow, hx, hz]

theorem inflatedRVValues_append {n r : ℕ} (z : Fin n → (CanonicalRV.RVSort M)ˣ)
    (u : Fin r → (CanonicalRV.RVSort M)ˣ) :
    rvUnitTupleValues (Fin.append z u) = Fin.append (rvUnitTupleValues z) (rvUnitTupleValues u) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [rvUnitTupleValues, Fin.append_left]
  · simp only [rvUnitTupleValues, Fin.append_right]

theorem inflatedRVValues_monomial {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℤ)
    (x : Fin b → (CanonicalRV.RVSort M)ˣ) :
    rvUnitTupleValues (integerMonomialMap A x) = integerMonomialMap A (rvUnitTupleValues x) :=
  inflatedMonomial_map rvUnitValueHom A x

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

/-- The image of an original-ground set of RV units under an integer
monomial map is original-ground definable. -/
def inflatedMonomialImage {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℤ)
    (V : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) b)) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) a) where
  carrier := integerMonomialMap A '' V.carrier
  definable := by
    apply (V.definable.image (rvUnitRectangularMonomialMap B.real A)).congr
    intro y
    rfl

/-- The value image of an original-ground set of RV units after an integer
monomial map. -/
def inflatedMonomialValueImage {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℤ)
    (S : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) b)) :
    GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin a)) where
  carrier := (fun x => rvUnitTupleValues (integerMonomialMap A x)) '' S.carrier
  definable := by
    apply ((inflatedMonomialImage A S).definable.image (rvUnitGammaMap hc B.real a)).congr
    intro γ
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨integerMonomialMap A x, ⟨x, hx, rfl⟩, rfl⟩

/-- A relative monomial chart of `X ⊆ (RV^×)^n × (RV^×)^r`: the coordinate
change `matrix` (with integer inverse) acts on `u` only; its first
`fixedArity` coordinates lie in the fixed residue set and the rest is a value
condition through `gamma ⊆ Γ^n × Γ^freeArity`. -/
structure RelativeMonomialChart (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n + r))) where
  fixedArity : ℕ
  freeArity : ℕ
  arity_eq : fixedArity + freeArity = r
  matrix : Matrix (Fin (fixedArity + freeArity)) (Fin r) ℤ
  inverse : Matrix (Fin r) (Fin (fixedArity + freeArity)) ℤ
  matrix_mul_inverse : matrix * inverse = 1
  inverse_mul_matrix : inverse * matrix = 1
  residue : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) fixedArity)
  beta : Fin fixedArity → Values.Gamma (M := M)
  beta_definable : ∀ i, GammaDefinableClosureAtBase B (beta i)
  residue_values : rvUnitTupleValues '' residue.carrier = {beta}
  residue_nonempty : residue.carrier.Nonempty
  gamma : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + freeArity)))
  source : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n + r))
  source_subset : source.carrier ⊆ X.carrier
  mem_iff : ∀ (z : Fin n → (CanonicalRV.RVSort M)ˣ) (u : Fin r → (CanonicalRV.RVSort M)ˣ),
    Fin.append z u ∈ source.carrier ↔
      inflatedTop matrix u ∈ residue.carrier ∧
        Fin.append (rvUnitTupleValues z) (rvUnitTupleValues (inflatedBottom matrix u)) ∈
          gamma.carrier

namespace RelativeMonomialChart
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n + r))}

/-- The chart source depends on `z` only through its values. -/
theorem source_invariant (C : RelativeMonomialChart X) (z z' : Fin n → (CanonicalRV.RVSort M)ˣ)
    (u : Fin r → (CanonicalRV.RVSort M)ˣ) (h : rvUnitTupleValues z = rvUnitTupleValues z') :
    Fin.append z u ∈ C.source.carrier ↔ Fin.append z' u ∈ C.source.carrier := by
  rw [C.mem_iff, C.mem_iff, h]

theorem residue_value (C : RelativeMonomialChart X) (w : Fin C.fixedArity → (CanonicalRV.RVSort M)ˣ)
    (hw : w ∈ C.residue.carrier) : rvUnitTupleValues w = C.beta := by
  have h : rvUnitTupleValues w ∈ rvUnitTupleValues '' C.residue.carrier := ⟨w, hw, rfl⟩
  rw [C.residue_values] at h
  exact h

theorem fixed_free_injective (C : RelativeMonomialChart X) (u u' : Fin r → (CanonicalRV.RVSort M)ˣ)
    (h1 : inflatedTop C.matrix u = inflatedTop C.matrix u')
    (h2 : inflatedBottom C.matrix u = inflatedBottom C.matrix u') : u = u' := by
  apply inflatedMonomial_injective C.matrix C.inverse C.inverse_mul_matrix
  rw [← inflatedTop_append_bottom, ← inflatedTop_append_bottom, h1, h2]

end RelativeMonomialChart

variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n + r))}

/-- Each Lemma 5.12 piece of a `z`-value-invariant set is a relative chart. -/
theorem GroundMonomialPiece.exists_relative_chart
    (hX : ∀ (z z' : Fin n → (CanonicalRV.RVSort M)ˣ) (u : Fin r → (CanonicalRV.RVSort M)ˣ),
      rvUnitTupleValues z = rvUnitTupleValues z' → Fin.append z u ∈ X.carrier →
        Fin.append z' u ∈ X.carrier)
    (P : GroundMonomialPiece X) : ∃ C : RelativeMonomialChart X, C.source = P.source := by
  classical
  let m := P.split.zeroArity
  let f := P.split.freeArity
  let e : Fin (m + f) ≃ Fin (n + r) := finCongr P.arity_eq
  let Mb : Matrix (Fin (n + r)) (Fin (n + r)) ℤ := P.matrix.val
  let Mi : Matrix (Fin (n + r)) (Fin (n + r)) ℤ := P.matrix.inv
  let M' : Matrix (Fin (m + f)) (Fin (n + r)) ℤ := Mb.submatrix e id
  let Mi' : Matrix (Fin (n + r)) (Fin (m + f)) ℤ := Mi.submatrix id e
  have hM : M' * Mi' = 1 := by
    change Mb.submatrix e id * Mi.submatrix id e = 1
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, P.matrix.val_inv]
    exact Matrix.submatrix_one_equiv e
  have hinj : Function.Injective (integerMonomialMap (G := (CanonicalRV.RVSort M)ˣ) Mb) :=
    inflatedMonomial_injective Mb Mi P.matrix.inv_val
  have hsplit : ∀ x : Fin (n + r) → (CanonicalRV.RVSort M)ˣ,
      P.blockSplit (integerMonomialMap Mb x) = (inflatedTop M' x, inflatedBottom M' x) := by
    intro x
    rfl
  have hS : ∀ x, x ∈ P.source.carrier ↔ inflatedTop M' x ∈ P.residue.carrier ∧
      (fun i => rvUnitValueHom (inflatedBottom M' x i)) ∈ P.gamma.carrier := by
    intro x
    have himg := P.matrix_image
    constructor
    · intro hx
      have hmem : integerMonomialMap Mb x ∈ integerMonomialMap P.matrix.val '' P.source.carrier :=
        ⟨x, hx, rfl⟩
      rw [himg] at hmem
      change P.blockSplit (integerMonomialMap Mb x) ∈ P.residue.carrier ×ˢ
        {y | rvUnitTupleValues y ∈ P.gamma.carrier} at hmem
      rw [hsplit] at hmem
      exact hmem
    · intro hx
      have hmem : integerMonomialMap Mb x ∈ P.blockSplit ⁻¹'
          (P.residue.prod (gammaGroundRVUnitGammaPreimage P.gamma)).carrier := by
        change P.blockSplit (integerMonomialMap Mb x) ∈ P.residue.carrier ×ˢ
          {y | rvUnitTupleValues y ∈ P.gamma.carrier}
        rw [hsplit]
        exact hx
      rw [← himg] at hmem
      obtain ⟨y, hy, hyx⟩ := hmem
      rwa [← hinj hyx]
  have hV : ∀ t ∈ P.residue.carrier, (fun i => rvUnitValueHom (t i)) = P.beta := by
    intro t ht
    have h : rvUnitTupleValues t ∈ rvUnitTupleValues '' P.residue.carrier := ⟨t, ht, rfl⟩
    rw [P.residue_values] at h
    exact h
  have hinv : ∀ (z z' : Fin n → (CanonicalRV.RVSort M)ˣ) (u : Fin r → (CanonicalRV.RVSort M)ˣ),
      (fun i => rvUnitValueHom (z i)) = (fun i => rvUnitValueHom (z' i)) →
        Fin.append z u ∈ P.source.carrier → Fin.append z' u ∈ P.source.carrier := by
    intro z z' u hz hx
    rw [P.source_cut] at hx ⊢
    refine ⟨hX z z' u hz hx.1, ?_⟩
    have hv : rvUnitTupleValues (Fin.append z' u) = rvUnitTupleValues (Fin.append z u) := by
      rw [inflatedRVValues_append, inflatedRVValues_append]
      exact congrArg (fun w => Fin.append w (rvUnitTupleValues u)) hz.symm
    change rvUnitTupleValues (Fin.append z' u) ∈ P.values.carrier
    rw [hv]
    exact hx.2
  obtain ⟨h, ℓ, N, Ninv, Qt, hN, hN', hdim, hfwd, hbwd⟩ :=
    inflated_relative_block_chart rvUnitValueHom rvUnitValueHom_surjective
      inflatedRVResidue_divisible M' Mi' hM P.residue.carrier P.beta hV P.gamma.carrier
      P.gamma_nonempty P.source.carrier hS hinv
  let D : Matrix (Fin (n + ℓ)) (Fin (n + r)) ℤ :=
    inflatedBlockDiag (1 : Matrix (Fin n) (Fin n) ℤ) (N.submatrix (Fin.natAdd h) id)
  have hD : ∀ (z : Fin n → (CanonicalRV.RVSort M)ˣ) (u : Fin r → (CanonicalRV.RVSort M)ˣ),
      rvUnitTupleValues (integerMonomialMap D (Fin.append z u)) =
        Fin.append (rvUnitTupleValues z) (rvUnitTupleValues (inflatedBottom N u)) := by
    intro z u
    rw [inflatedBlockDiag_monomial, integerMonomialMap_one, inflatedRVValues_append]
    rfl
  let W := inflatedMonomialImage Qt P.residue
  let J := inflatedMonomialValueImage D P.source
  obtain ⟨t0, ht0⟩ := P.residue_nonempty
  refine ⟨{
    fixedArity := h
    freeArity := ℓ
    arity_eq := hdim
    matrix := N
    inverse := Ninv
    matrix_mul_inverse := hN
    inverse_mul_matrix := hN'
    residue := W
    beta := integerMonomialMap Qt P.beta
    beta_definable := fun i =>
      inflatedMonomial_mem (DiamondIntegral.Section4.GammaNamesSubgroup.namesSubgroup B) Qt P.beta
        P.beta_definable i
    residue_values := by
      apply Set.Subset.antisymm
      · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
        change rvUnitTupleValues (integerMonomialMap Qt t) = integerMonomialMap Qt P.beta
        rw [inflatedRVValues_monomial]
        exact congrArg (integerMonomialMap Qt) (hV t ht)
      · rintro _ rfl
        refine ⟨integerMonomialMap Qt t0, ⟨t0, ht0, rfl⟩, ?_⟩
        rw [inflatedRVValues_monomial]
        exact congrArg (integerMonomialMap Qt) (hV t0 ht0)
    residue_nonempty := ⟨integerMonomialMap Qt t0, t0, ht0, rfl⟩
    gamma := J
    source := P.source
    source_subset := by
      intro x hx
      rw [P.source_cut] at hx
      exact hx.1
    mem_iff := by
      intro z u
      constructor
      · intro hx
        exact ⟨hfwd z u hx, Fin.append z u, hx, hD z u⟩
      · rintro ⟨hW, x', hx', hval⟩
        obtain ⟨z', u', rfl⟩ : ∃ z' u', x' = Fin.append z' u' :=
          ⟨_, _, (inflated_append_split x').symm⟩
        change rvUnitTupleValues (integerMonomialMap D (Fin.append z' u')) = _ at hval
        rw [hD] at hval
        obtain ⟨hz, hy⟩ := (inflated_append_eq_iff _ _ _ _).mp hval
        exact hbwd z u z' u' hx' hW hz.symm hy.symm }, rfl⟩

/-- Relative monomial decomposition: a `z`-value-invariant original-ground set
of nonzero RV tuples `(z,u)` is a finite disjoint union of relative chart
sources. -/
theorem relative_monomial_decomposition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n + r)))
    (hX : ∀ (z z' : Fin n → (CanonicalRV.RVSort M)ˣ) (u : Fin r → (CanonicalRV.RVSort M)ˣ),
      rvUnitTupleValues z = rvUnitTupleValues z' → Fin.append z u ∈ X.carrier →
        Fin.append z' u ∈ X.carrier) :
    ∃ N : ℕ, ∃ C : Fin N → RelativeMonomialChart X,
      (∀ i j, i ≠ j → Disjoint (C i).source.carrier (C j).source.carrier) ∧
      (∀ x, x ∈ X.carrier ↔ ∃ j, x ∈ (C j).source.carrier) := by
  obtain ⟨N, P, hd, hcov, -⟩ := monomial_decomposition_5_12 hκ hs h00 hsmall hγsmall hΓ X
  choose C hC using fun j => (P j).exists_relative_chart hX
  refine ⟨N, C, ?_, ?_⟩
  · intro i j hij
    rw [hC i, hC j]
    apply Set.disjoint_left.mpr
    intro x hi hj
    rw [(P i).source_cut] at hi
    rw [(P j).source_cut] at hj
    exact Set.disjoint_left.mp (hd i j hij) hi.2 hj.2
  · intro x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := (hcov (rvUnitTupleValues x)).mp ⟨x, hx, rfl⟩
      refine ⟨j, ?_⟩
      rw [hC j, (P j).source_cut]
      exact ⟨hx, hj⟩
    · rintro ⟨j, hj⟩
      rw [hC j, (P j).source_cut] at hj
      exact hj.1

end DiamondIntegral.Section5
