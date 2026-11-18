import «section 4».GammaEndpointInvariant
import «section 3».TensorCoefficientRelations
import «section 3».GammaGroundFiniteGammaSemiringSquare
import «section 3».GammaGroundRESGradedSemiring

/-! Nontriviality of the coefficient-translation kernel in Proposition 3.18
(the T001 audit's counterexample to the original "isomorphism" claim).

A balanced detector on the unmeasured tensor
`K₊RES[*] ⊗_{K₊Γ^fin[*]} K₊Γ[*]` with values in the dual numbers `ℤ[ε]`:
* on RES, the number of points in degree zero (and `0` in higher degrees);
* on Γ, the number of points in degree zero, the odd endpoint invariant
  times `ε` in degree one, and `0` in higher degrees.
Both agree on the finite Γ coefficients (finite unary sets have no
endpoint germs). For a nonempty finite RES coefficient `X` of constant
value `δ` with `δ²` outside the subgroup of translation constants, the
elementary pair `[X] ⊗ [(1,∞)]`, `[X] ⊗ [(δ,∞)]` lies in the kernel of Ψ
but is separated by the detector. The Γ-side invariance uses the piecewise
unimodular classification of Gamma morphisms and hence the accepted
Reichstein--Youssin input (Remark 3.15). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section4.ResiduePurity
open DiamondIntegral.Section3
open scoped TensorProduct

namespace DiamondIntegral.Section4.Proposition318Witness
open GermJumps GammaEndpointInvariant

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-! ### Degree-zero counts -/

theorem card_set_zero (I : Set (Fin 0 → Values.Gamma (M := M))) :
    Nat.card I = if I.Nonempty then 1 else 0 := by
  by_cases h : I.Nonempty
  · rw [if_pos h]
    obtain ⟨x, hx⟩ := h
    haveI : Subsingleton I := ⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨⟨x, hx⟩⟩⟩
  · rw [if_neg h]
    exact Nat.card_eq_zero.mpr (Or.inl ⟨fun a => h ⟨a.val, a.property⟩⟩)

instance finite_piece_zero (I : GammaGroundGammaPiece hc B 0) : Finite I := by
  haveI : Subsingleton I := ⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩
  exact Finite.of_subsingleton

theorem card_carrier_zero (A : GammaGroundGammaObject hc B 0) :
    Nat.card A.Carrier = ∑ i, Nat.card (A.piece i) :=
  Nat.card_sigma

theorem card_rvLift_zero (A : GammaGroundGammaObject hc B 0) :
    Nat.card A.rvLift.domain = Nat.card A.Carrier := by
  have hdec : Function.Bijective A.decode := by
    refine ⟨?_, A.decode_surjective⟩
    rintro ⟨i, c⟩ ⟨i', c'⟩ h
    have hi : i = i' := congrArg Sigma.fst h
    subst hi
    have hc : c = c' := Subtype.ext (Subtype.ext (funext fun ij => ij.1.elim0))
    rw [hc]
  exact Nat.card_congr (A.rvPieces.rvEquiv.symm.trans
    (A.rvCodeBijection.equiv.symm.trans (Equiv.ofBijective _ hdec)))

theorem objNu_empty (χ : Values.Gamma (M := M) → ℤ) (k : ℕ) :
    objNu χ (GammaGroundGammaObject.empty hc B k) = 0 := by
  simp [objNu, GammaGroundGammaObject.empty]

theorem card_empty (k : ℕ) : Nat.card (GammaGroundGammaObject.empty hc B k).Carrier = 0 :=
  Nat.card_eq_zero.mpr (Or.inl ⟨fun a => a.1.elim0⟩)

theorem pieceLine_finite (P : GammaGroundGammaPiece hc B 1) (hP : P.carrier.Finite) :
    (pieceLine P).Finite :=
  hP.preimage (fun x _ y _ h => congrFun h 0)

/-! ### Products with degree-zero objects -/

theorem append_zero_left (u : Fin 0 → Values.Gamma (M := M)) (v : Fin 1 → Values.Gamma (M := M)) :
    (Fin.append u v : Fin (0 + 1) → Values.Gamma (M := M)) = v := by
  funext i
  have hi : i = Fin.natAdd 0 (0 : Fin 1) := by fin_cases i; rfl
  subst hi
  rw [Fin.append_right]
  rfl

theorem append_zero_right (v : Fin 1 → Values.Gamma (M := M)) (u : Fin 0 → Values.Gamma (M := M)) :
    (Fin.append v u : Fin (1 + 0) → Values.Gamma (M := M)) = v := by
  funext i
  have hi : i = Fin.castAdd 0 (0 : Fin 1) := by fin_cases i; rfl
  subst hi
  rw [Fin.append_left]
  rfl

theorem pieceLine_product_zero_one (a : GammaGroundGammaPiece hc B 0) (b : GammaGroundGammaPiece hc B 1) :
    pieceLine (k := 0 + 1) (gammaGroundGammaAppendMap a b).image =
      if a.carrier.Nonempty then pieceLine b else ∅ := by
  ext x
  rw [mem_pieceLine]
  constructor
  · rintro ⟨p, hp⟩
    have hp' : Fin.append p.val.1 p.val.2 = (fun _ => x) := hp
    rw [append_zero_left] at hp'
    have hne : a.carrier.Nonempty := ⟨p.val.1, p.property.1⟩
    rw [if_pos hne, mem_pieceLine]
    convert p.property.2 using 1
    exact hp'.symm
  · intro hx
    by_cases hne : a.carrier.Nonempty
    · rw [if_pos hne, mem_pieceLine] at hx
      obtain ⟨u, hu⟩ := hne
      exact ⟨⟨(u, fun _ => x), hu, hx⟩, append_zero_left u _⟩
    · rw [if_neg hne] at hx
      exact hx.elim

theorem pieceLine_product_one_zero (b : GammaGroundGammaPiece hc B 1) (a : GammaGroundGammaPiece hc B 0) :
    pieceLine (k := 1 + 0) (gammaGroundGammaAppendMap b a).image =
      if a.carrier.Nonempty then pieceLine b else ∅ := by
  ext x
  rw [mem_pieceLine]
  constructor
  · rintro ⟨p, hp⟩
    have hp' : Fin.append p.val.1 p.val.2 = (fun _ => x) := hp
    rw [append_zero_right] at hp'
    have hne : a.carrier.Nonempty := ⟨p.val.2, p.property.2⟩
    rw [if_pos hne, mem_pieceLine]
    convert p.property.1 using 1
    exact hp'.symm
  · intro hx
    by_cases hne : a.carrier.Nonempty
    · rw [if_pos hne, mem_pieceLine] at hx
      obtain ⟨u, hu⟩ := hne
      exact ⟨⟨(fun _ => x, u), hx, hu⟩, append_zero_right _ u⟩
    · rw [if_neg hne] at hx
      exact hx.elim

theorem product_piece {k l : ℕ} (A : GammaGroundGammaObject hc B k) (D : GammaGroundGammaObject hc B l)
    (p : Fin A.tags × Fin D.tags) :
    (A.product D).piece (finProdFinEquiv p) = (gammaGroundGammaAppendMap (A.piece p.1) (D.piece p.2)).image := by
  change (gammaGroundGammaAppendMap (A.piece (finProdFinEquiv.symm (finProdFinEquiv p)).1)
    (D.piece (finProdFinEquiv.symm (finProdFinEquiv p)).2)).image = _
  rw [Equiv.symm_apply_apply]

theorem objNu_product_zero_one (χ : Values.Gamma (M := M) → ℤ)
    (a : GammaGroundGammaObject hc B 0) (b : GammaGroundGammaObject hc B 1) :
    objNu χ (a.product b) = (Nat.card a.Carrier : ℤ) * objNu χ b := by
  rw [objNu_def, objNu_def, card_carrier_zero]
  change ∑ i : Fin (a.tags * b.tags), weightedJump χ (pieceLine ((a.product b).piece i)) = _
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [product_piece, pieceLine_product_zero_one, Fintype.sum_prod_type]
  rw [Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [card_set_zero]
  by_cases h : (a.piece i).carrier.Nonempty
  · simp only [if_pos h, Nat.cast_one, one_mul]
  · simp only [if_neg h, weightedJump_empty, Finset.sum_const_zero, Nat.cast_zero, zero_mul]

theorem objNu_product_one_zero (χ : Values.Gamma (M := M) → ℤ)
    (b : GammaGroundGammaObject hc B 1) (a : GammaGroundGammaObject hc B 0) :
    objNu χ (b.product a) = objNu χ b * (Nat.card a.Carrier : ℤ) := by
  rw [objNu_def, objNu_def, card_carrier_zero]
  change ∑ i : Fin (b.tags * a.tags), weightedJump χ (pieceLine ((b.product a).piece i)) = _
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [product_piece, pieceLine_product_one_zero, Fintype.sum_prod_type]
  rw [Nat.cast_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [card_set_zero]
  by_cases h : (a.piece j).carrier.Nonempty
  · simp only [if_pos h, Nat.cast_one, mul_one]
  · simp only [if_neg h, weightedJump_empty, Nat.cast_zero, mul_zero]

theorem card_product (A : GammaGroundGammaObject hc B 0) (D : GammaGroundGammaObject hc B 0) :
    Nat.card (A.product D).Carrier = Nat.card A.Carrier * Nat.card D.Carrier := by
  rw [Nat.card_congr (A.productCarrierEquiv D), Nat.card_prod]

/-! ### The graded Gamma invariant -/

def gradedValue (χ : Values.Gamma (M := M) → ℤ) (A : GammaGroundGradedGammaObject hc B) : DualNumber ℤ :=
  if A.1 = 0 then TrivSqZeroExt.inl (Nat.card A.2.Carrier : ℤ)
  else if A.1 = 1 then TrivSqZeroExt.inr (objNu χ A.2) else 0

theorem gradedValue_empty (χ : Values.Gamma (M := M) → ℤ) (k : ℕ) :
    gradedValue χ ⟨k, GammaGroundGammaObject.empty hc B k⟩ = 0 := by
  simp only [gradedValue, card_empty, objNu_empty, Nat.cast_zero, TrivSqZeroExt.inl_zero,
    TrivSqZeroExt.inr_zero, ite_self]

theorem gradedValue_zero (χ : Values.Gamma (M := M) → ℤ) (A : GammaGroundGammaObject hc B 0) :
    gradedValue χ ⟨0, A⟩ = TrivSqZeroExt.inl (Nat.card A.Carrier : ℤ) := by
  unfold gradedValue
  rw [if_pos rfl]

theorem gradedValue_one (χ : Values.Gamma (M := M) → ℤ) (A : GammaGroundGammaObject hc B 1) :
    gradedValue χ ⟨1, A⟩ = TrivSqZeroExt.inr (objNu χ A) := by
  unfold gradedValue
  rw [if_neg one_ne_zero, if_pos rfl]

theorem gradedValue_high (χ : Values.Gamma (M := M) → ℤ) {k : ℕ} (hk : 2 ≤ k) (A : GammaGroundGammaObject hc B k) :
    gradedValue χ ⟨k, A⟩ = 0 := by
  unfold gradedValue
  rw [if_neg (show ¬ k = 0 by omega), if_neg (show ¬ k = 1 by omega)]

theorem card_unit : Nat.card (GammaGroundGammaObject.unit hc B).Carrier = 1 := by
  rw [card_carrier_zero]
  simp only [GammaGroundGammaObject.unit, Fin.sum_univ_one]
  rw [card_set_zero, if_pos]
  exact ⟨fun i => i.elim0, Set.mem_univ _⟩

theorem scissor_card (U : GammaGroundGammaObject hc B 0)
    (X : Fin U.tags → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin 0)))
    (hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier) :
    Nat.card (U.restrict X).Carrier + Nat.card (U.restrict (U.difference X)).Carrier = Nat.card U.Carrier := by
  rw [card_carrier_zero, card_carrier_zero, card_carrier_zero]
  simp only [GammaGroundGammaObject.restrict, GammaGroundGammaObject.difference]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hfin : (U.piece i).carrier.Finite := Set.toFinite _
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  change (X i).carrier.ncard + ((U.piece i).carrier ∩ (X i).carrierᶜ).ncard = (U.piece i).carrier.ncard
  rw [← Set.diff_eq, add_comm]
  exact Set.ncard_diff_add_ncard_of_subset (hX i) hfin

theorem scissor_nu (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (χ : Values.Gamma (M := M) → ℤ) (U : GammaGroundGammaObject hc B 1)
    (X : Fin U.tags → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin 1)))
    (hX : ∀ i, (X i).carrier ⊆ (U.piece i).carrier) :
    objNu χ (U.restrict X) + objNu χ (U.restrict (U.difference X)) = objNu χ U := by
  rw [objNu_def, objNu_def, objNu_def]
  simp only [GammaGroundGammaObject.restrict, GammaGroundGammaObject.difference]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hd : Disjoint (pieceLine (X i)) (pieceLine ((U.piece i).sdiff (X i))) :=
    Set.disjoint_left.mpr (fun x hx hx' => hx'.2 hx)
  have hu : pieceLine (U.piece i) = pieceLine (X i) ∪ pieceLine ((U.piece i).sdiff (X i)) := by
    ext x
    rw [Set.mem_union, mem_pieceLine, mem_pieceLine, mem_pieceLine]
    change _ ↔ _ ∨ (_ ∧ _)
    constructor
    · intro h
      by_cases h' : (fun _ => x) ∈ (X i).carrier
      · exact Or.inl h'
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h)
      · exact hX i h
      · exact h.1
  rw [hu, weightedJump_union χ hd (tame_pieceLine h00 hκ hs hr hγ (X i)) (tame_pieceLine h00 hκ hs hr hγ _)]

/-- The Gamma-side invariant. -/
def gammaInvariant [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin 1 → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (δ : Values.Gamma (M := M)) :
    PositiveGrothendieck.Invariant (gammaGroundGammaSemiringPresentation hc B) (R := DualNumber ℤ) where
  toFun := gradedValue (chi (translationSubgroup hc B) δ)
  iso := by
    rintro _ _ ⟨k, a, b, ⟨e⟩, rfl, rfl⟩
    have f : GammaGroundGammaHom a b := e.hom
    rcases k with _ | _ | k
    · rw [gradedValue_zero, gradedValue_zero, Nat.card_congr f.bijection.equiv]
    · change gradedValue _ ⟨1, a⟩ = gradedValue _ ⟨1, b⟩
      rw [gradedValue_one, gradedValue_one]
      exact congrArg TrivSqZeroExt.inr (objNu_iso hκ hs h00 hsmall hγsmall RY _
        (fun c hc e => chi_mul _ δ hc e) (fun c hc e => chi_inv_mul _ δ hc e) f)
    · rw [gradedValue_high (k := k + 1 + 1) _ (by omega), gradedValue_high (k := k + 1 + 1) _ (by omega)]
  empty := gradedValue_empty _ 0
  unit := by
    change gradedValue _ ⟨0, GammaGroundGammaObject.unit hc B⟩ = 1
    rw [gradedValue_zero, card_unit, Nat.cast_one, TrivSqZeroExt.inl_one]
  product := by
    rintro ⟨k, a⟩ ⟨l, b⟩
    change gradedValue _ ⟨k + l, a.product b⟩ = gradedValue _ ⟨k, a⟩ * gradedValue _ ⟨l, b⟩
    rcases k with _ | _ | k <;> rcases l with _ | _ | l
    · change gradedValue _ ⟨0, a.product b⟩ = gradedValue _ ⟨0, a⟩ * gradedValue _ ⟨0, b⟩
      rw [gradedValue_zero, gradedValue_zero, gradedValue_zero, card_product, Nat.cast_mul,
        TrivSqZeroExt.inl_mul]
    · change gradedValue _ ⟨1, a.product b⟩ = gradedValue _ ⟨0, a⟩ * gradedValue _ ⟨1, b⟩
      rw [gradedValue_one, gradedValue_zero, gradedValue_one, TrivSqZeroExt.inl_mul_inr, smul_eq_mul]
      exact congrArg TrivSqZeroExt.inr (objNu_product_zero_one _ a b)
    · rw [gradedValue_high (k := 0 + (l + 1 + 1)) _ (by omega), gradedValue_high (k := l + 1 + 1) _ (by omega),
        mul_zero]
    · change gradedValue _ ⟨1, a.product b⟩ = gradedValue _ ⟨1, a⟩ * gradedValue _ ⟨0, b⟩
      rw [gradedValue_one, gradedValue_one, gradedValue_zero, TrivSqZeroExt.inr_mul_inl,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      exact congrArg TrivSqZeroExt.inr (objNu_product_one_zero _ a b)
    · change gradedValue _ ⟨2, a.product b⟩ = gradedValue _ ⟨1, a⟩ * gradedValue _ ⟨1, b⟩
      rw [gradedValue_high _ (le_refl 2), gradedValue_one, gradedValue_one, TrivSqZeroExt.inr_mul_inr]
    · rw [gradedValue_high (k := 0 + 1 + (l + 1 + 1)) _ (by omega), gradedValue_high (k := l + 1 + 1) _ (by omega),
        mul_zero]
    · rw [gradedValue_high (k := k + 1 + 1 + 0) _ (by omega), gradedValue_high (k := k + 1 + 1) _ (by omega),
        zero_mul]
    · rw [gradedValue_high (k := k + 1 + 1 + (0 + 1)) _ (by omega), gradedValue_high (k := k + 1 + 1) _ (by omega),
        zero_mul]
    · rw [gradedValue_high (k := k + 1 + 1 + (l + 1 + 1)) _ (by omega), gradedValue_high (k := k + 1 + 1) _ (by omega),
        zero_mul]
  scissor := by
    rintro _ _ _ _ (⟨k, a, b, d, e, ⟨U, X, hX, ha, hb, hd, he⟩, rfl, rfl, rfl, rfl⟩ | ⟨k, rfl, rfl, rfl, rfl⟩)
    · subst ha hb he
      subst d
      rw [gradedValue_empty, add_zero]
      rcases k with _ | _ | k
      · rw [gradedValue_zero, gradedValue_zero, gradedValue_zero, ← TrivSqZeroExt.inl_add,
          ← Nat.cast_add, scissor_card U X hX]
      · change gradedValue _ ⟨1, U.restrict X⟩ + gradedValue _ ⟨1, U.restrict (U.difference X)⟩ =
          gradedValue _ ⟨1, U⟩
        rw [gradedValue_one, gradedValue_one, gradedValue_one, ← TrivSqZeroExt.inr_add,
          scissor_nu h00 hκ.le hs hsmall hγsmall _ U X hX]
      · rw [gradedValue_high (k := k + 1 + 1) _ (by omega), gradedValue_high (k := k + 1 + 1) _ (by omega),
          gradedValue_high (k := k + 1 + 1) _ (by omega), add_zero]
    · simp only [gradedValue_empty]

def gammaPsi [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin 1 → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (δ : Values.Gamma (M := M)) : GammaGroundGammaPositiveSemiring hc B →+* DualNumber ℤ :=
  PositiveGrothendieck.lift _ (gammaInvariant hκ hs h00 hsmall hγsmall RY δ)

theorem gammaPsi_class [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin 1 → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (δ : Values.Gamma (M := M)) {k : ℕ} (A : GammaGroundGammaObject hc B k) :
    gammaPsi hκ hs h00 hsmall hγsmall RY δ (gammaGroundGammaSemiringClass A) =
      gradedValue (chi (translationSubgroup hc B) δ) ⟨k, A⟩ := by
  have h := PositiveGrothendieck.lift_of (gammaGroundGammaSemiringPresentation hc B)
    (gammaInvariant hκ hs h00 hsmall hγsmall RY δ) ⟨k, A⟩
  exact h

/-! ### The RES-side count -/

def resCard (U : GammaGroundRESObject hc B 0) : ℕ := Nat.card U.obj.domain

theorem rv_domain_finite (U : GammaGroundRVObject hc B 0) : Finite U.domain := by
  let b0 : GammaGroundDefSet.univ hc B (rawRVSpace (M := M) 0) :=
    ⟨fun i => i.elim0, Set.mem_univ _⟩
  have hsub : ∀ t : GammaGroundDefSet.univ hc B (rawRVSpace (M := M) 0), t = b0 :=
    fun t => Subtype.ext (funext fun i => i.elim0)
  have h := U.finite b0
  have huniv : {a : U.domain | U.volume a = b0} = Set.univ := Set.eq_univ_of_forall (fun a => hsub _)
  rw [huniv] at h
  exact Set.finite_univ_iff.mp h

def resInvariant : PositiveAdditiveGrothendieck.Invariant (gammaGroundRESPresentation hc B 0) (A := ℕ) where
  toFun := resCard
  iso := by
    rintro a b ⟨e⟩
    let f := ((gammaGroundResProperty (hc := hc) (ground := B) (k := 0)).ι.mapIso e).hom
    exact Nat.card_eq_of_bijective _ (show Function.Bijective (fun x => (show GammaGroundBijection a.obj.domain b.obj.domain from f).map x) from
      (show GammaGroundBijection a.obj.domain b.obj.domain from f).bijective)
  empty := by
    change Nat.card (GammaGroundDefSet.empty hc B (rawRVSpace (M := M) 0)) = 0
    exact Nat.card_eq_zero.mpr (Or.inl ⟨fun a => a.property⟩)
  scissor := by
    rintro a b d e ⟨U, X, hX, ha, hb, hd, he⟩
    haveI : Finite U.domain := hd ▸ rv_domain_finite d.obj
    have hfin : U.domain.carrier.Finite := Set.toFinite _
    unfold resCard
    rw [ha, hb, hd, he]
    change Nat.card X + Nat.card (U.domain.sdiff X) = Nat.card U.domain +
      Nat.card (GammaGroundDefSet.empty hc B (rawRVSpace (M := M) 0))
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    change X.carrier.ncard + (U.domain.carrier ∩ X.carrierᶜ).ncard = U.domain.carrier.ncard +
      (∅ : Set (rawRVSpace (M := M) 0).Carrier).ncard
    rw [Set.ncard_empty, add_zero, ← Set.diff_eq, add_comm]
    exact Set.ncard_diff_add_ncard_of_subset hX hfin

def cardHom : GammaGroundRESKPlus hc B 0 →+ ℕ :=
  PositiveAdditiveGrothendieck.lift _ (resInvariant (hc := hc) (B := B))

theorem cardHom_class (U : GammaGroundRESObject hc B 0) : cardHom (gammaGroundRESClass U) = resCard U :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem resCard_product (U V : GammaGroundRESObject hc B 0) :
    resCard (U.product V) = resCard U * resCard V := by
  unfold resCard
  let f := gammaGroundRVPackBijection U.obj.domain V.obj.domain
  change Nat.card (gammaGroundRVProductDomain U.obj.domain V.obj.domain) = _
  rw [← Nat.card_eq_of_bijective _ f.bijective]
  change Nat.card ↥(U.obj.domain.carrier ×ˢ V.obj.domain.carrier) = _
  rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]

theorem cardHom_mul (a b : GammaGroundRESKPlus hc B 0) :
    cardHom (gammaGroundRESClassMul a b) = cardHom a * cardHom b := by
  change cardHom (gammaGroundRESClass ((gammaGroundRESRepresentative a).product (gammaGroundRESRepresentative b))) = _
  rw [cardHom_class, resCard_product, ← cardHom_class, ← cardHom_class,
    gammaGroundRESRepresentative_class, gammaGroundRESRepresentative_class]

theorem resCard_unit : resCard (GammaGroundRESObject.unit hc B) = 1 := by
  unfold resCard
  change Nat.card (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) 0)) = 1
  haveI : Subsingleton (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) 0)) :=
    ⟨fun s t => Subtype.ext (funext fun i => i.elim0)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨⟨fun i => i.elim0, Set.mem_univ _⟩⟩⟩

def resPhi : GammaGroundRESDirectSum hc B →+* DualNumber ℤ where
  toFun x := TrivSqZeroExt.inl ((cardHom (x 0) : ℕ) : ℤ)
  map_zero' := by simp
  map_add' x y := by
    simp only [DirectSum.add_apply, map_add, Nat.cast_add, TrivSqZeroExt.inl_add]
  map_one' := by
    rw [DirectSum.one_def, DirectSum.of_eq_same]
    change TrivSqZeroExt.inl ((cardHom (gammaGroundRESClass (GammaGroundRESObject.unit hc B)) : ℕ) : ℤ) = 1
    rw [cardHom_class, resCard_unit, Nat.cast_one, TrivSqZeroExt.inl_one]
  map_mul' x y := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i a =>
      induction y using DirectSum.induction_on with
      | zero => simp
      | of j b =>
        rw [DirectSum.of_mul_of]
        by_cases hij : i = 0 ∧ j = 0
        · obtain ⟨rfl, rfl⟩ := hij
          rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
          change TrivSqZeroExt.inl ((cardHom (gammaGroundRESClassMul a b) : ℕ) : ℤ) = _
          rw [cardHom_mul, Nat.cast_mul, TrivSqZeroExt.inl_mul]
          rfl
        · have hne : (0 : ℕ) ≠ i + j := by omega
          rw [DirectSum.of_eq_of_ne _ _ _ hne, map_zero, Nat.cast_zero, TrivSqZeroExt.inl_zero]
          rcases not_and_or.mp hij with hi | hj
          · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hi), map_zero, Nat.cast_zero,
              TrivSqZeroExt.inl_zero, zero_mul]
          · rw [DirectSum.of_eq_of_ne (β := GammaGroundRESKPlus hc B) _ _ _ (Ne.symm hj), map_zero,
              Nat.cast_zero, TrivSqZeroExt.inl_zero, mul_zero]
      | add b c hb hc => simp only [mul_add, DirectSum.add_apply, map_add, Nat.cast_add,
          TrivSqZeroExt.inl_add] at hb hc ⊢; rw [hb, hc]
    | add a c ha hc => simp only [add_mul, DirectSum.add_apply, map_add, Nat.cast_add,
        TrivSqZeroExt.inl_add] at ha hc ⊢; rw [ha, hc]

theorem resPhi_class (X : GammaGroundRESObject hc B 0) :
    resPhi (gammaGroundRESDirectSumClass X) = TrivSqZeroExt.inl (Nat.card X.obj.domain : ℤ) := by
  change TrivSqZeroExt.inl ((cardHom ((DirectSum.of _ 0 (gammaGroundRESClass X)) 0) : ℕ) : ℤ) = _
  rw [DirectSum.of_eq_same, cardHom_class]
  rfl

/-! ### The balanced square and the detector -/

theorem detector_square [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin 1 → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (δ : Values.Gamma (M := M)) :
    (resPhi (hc := hc) (B := B)).comp
        (algebraMap (GammaGroundFiniteGammaPositiveSemiring hc B) (GammaGroundRESDirectSum hc B)) =
      (gammaPsi hκ hs h00 hsmall hγsmall RY δ).comp
        (algebraMap (GammaGroundFiniteGammaPositiveSemiring hc B) (GammaGroundGammaPositiveSemiring hc B)) := by
  apply PositiveGrothendieck.hom_ext (gammaGroundFiniteGammaSemiringPresentation hc B)
  rintro ⟨k, A⟩
  change resPhi (gammaGroundFiniteGammaToRESSemiring (gammaGroundFiniteGammaSemiringClass A)) =
    gammaPsi hκ hs h00 hsmall hγsmall RY δ (gammaGroundFiniteGammaToGammaSemiring (gammaGroundFiniteGammaSemiringClass A))
  rw [gammaGroundFiniteGammaToRESSemiring_class, gammaGroundFiniteGammaToGammaSemiring_class]
  rw [gammaPsi_class]
  by_cases h0 : k = 0
  · subst h0
    rw [resPhi_class, gradedValue_zero]
    change TrivSqZeroExt.inl (Nat.card A.obj.rvLift.domain : ℤ) = _
    rw [card_rvLift_zero]
  · change TrivSqZeroExt.inl ((cardHom ((DirectSum.of _ k (gammaGroundRESClass A.resLift)) 0) : ℕ) : ℤ) = _
    rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h0), map_zero, Nat.cast_zero, TrivSqZeroExt.inl_zero]
    by_cases h1 : k = 1
    · subst h1
      rw [gradedValue_one]
      have hz : objNu (chi (translationSubgroup hc B) δ) A.obj = 0 := by
        rw [objNu_def]
        apply Finset.sum_eq_zero
        intro i _
        exact weightedJump_of_finite _ (pieceLine_finite _ (A.property i))
      rw [hz, TrivSqZeroExt.inr_zero]
    · rw [gradedValue_high (k := k) _ (by omega)]

/-- The balanced detector on the unmeasured tensor. -/
def detector [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin 1 → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (δ : Values.Gamma (M := M)) : GammaGroundUnmeasuredPositiveTensor hc B →+* DualNumber ℤ :=
  balancedSquareMap resPhi (gammaPsi hκ hs h00 hsmall hγsmall RY δ)
    (detector_square hκ hs h00 hsmall hγsmall RY δ)

theorem gammaPsi_tail [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin 1 → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (δ a : Values.Gamma (M := M)) (ha : GammaDefinableClosureAtBase B a) :
    gammaPsi hκ hs h00 hsmall hγsmall RY δ
        (gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundGammaTail (hc := hc) a ha))) =
      TrivSqZeroExt.inr (chi (translationSubgroup hc B) δ a) := by
  rw [gammaPsi_class, gradedValue_one]
  congr 1
  rw [objNu_def]
  simp only [GammaGroundGammaObject.single, Fin.sum_univ_one]
  exact weightedJump_Ioi _ a

/-! ### The witness -/

/-- The elementary pair `[X] ⊗ [(1,∞)]`, `[X] ⊗ [(δ,∞)]`. -/
def pairLeft (X : GammaGroundRESObject hc B 0) : GammaGroundUnmeasuredPositiveTensor hc B :=
  gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundGammaPositiveTail (hc := hc) (B := B)))

def pairRight (X : GammaGroundRESObject hc B 0) (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) : GammaGroundUnmeasuredPositiveTensor hc B :=
  gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundGammaTail (hc := hc) δ hδ))

theorem pair_isCoefficientPair (X : GammaGroundRESObject hc B 0) (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) (hav : GammaGroundRESAvailableValueTuple X (fun _ : Fin 1 => δ)) :
    gammaGroundUnmeasuredCoefficientPair (pairLeft X) (pairRight X δ hδ) := by
  refine ⟨0, 1, 0, X, gammaGroundGammaPositiveTail, gammaGroundGammaTail δ hδ, fun _ => δ,
    fun j hj => absurd (Subsingleton.elim j 0) hj, fun _ => hδ, hav, ?_, rfl, rfl⟩
  intro g
  change 1 < g 0 ↔ δ < δ * g 0
  have h : δ * 1 < δ * g 0 ↔ 1 < g 0 := mul_lt_mul_iff_left δ
  rw [mul_one] at h
  exact h.symm

/-- **Proposition 3.18, nontriviality of the kernel.** For a nonempty
finite RES coefficient `X` of constant definable value `δ` whose square is
not a product of translation constants, the elementary coefficient pair
lies in the kernel of the unmeasured Ψ but its two members are distinct.
So Ψ is not injective and the coefficient congruence is nontrivial. -/
theorem proposition_3_18_unmeasured_kernel_nontrivial [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin 1 → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (X : GammaGroundRESObject hc B 0) (hX : Nonempty X.obj.domain)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ)
    (hav : GammaGroundRESAvailableValueTuple X (fun _ : Fin 1 => δ))
    (hδT : δ * δ ∉ translationSubgroup hc B) :
    gammaGroundUnmeasuredCoefficientPair (pairLeft X) (pairRight X δ hδ) ∧
      gammaGroundUnmeasuredTensorMap (pairLeft X) = gammaGroundUnmeasuredTensorMap (pairRight X δ hδ) ∧
      pairLeft X ≠ pairRight X δ hδ := by
  have hpair := pair_isCoefficientPair X δ hδ hav
  refine ⟨hpair, gammaGroundUnmeasuredCoefficientPair_valid hpair, ?_⟩
  intro heq
  have h := congrArg (detector hκ hs h00 hsmall hγsmall RY δ) heq
  simp only [detector, pairLeft, pairRight, balancedSquareMap_tmul, resPhi_class] at h
  have h1 : gammaGroundGammaPositiveTail (hc := hc) (B := B) = gammaGroundGammaTail 1 (gammaDefinableClosure_one B) := rfl
  rw [h1, gammaPsi_tail, gammaPsi_tail, chi_one, chi_self _ _ hδT, TrivSqZeroExt.inl_mul_inr,
    TrivSqZeroExt.inl_mul_inr, smul_eq_mul, smul_eq_mul, mul_zero, mul_one] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp only [TrivSqZeroExt.snd_inr] at h2
  have hpos : 0 < Nat.card X.obj.domain := by
    haveI : Finite X.obj.domain := rv_domain_finite X.obj
    exact Nat.card_pos
  omega

theorem gammaGroundUnmeasuredTensorMap_not_injective [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin 1 → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (X : GammaGroundRESObject hc B 0) (hX : Nonempty X.obj.domain)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ)
    (hav : GammaGroundRESAvailableValueTuple X (fun _ : Fin 1 => δ))
    (hδT : δ * δ ∉ translationSubgroup hc B) :
    ¬ Function.Injective (gammaGroundUnmeasuredTensorMap (hc := hc) (ground := B)) := by
  obtain ⟨_, he, hne⟩ := proposition_3_18_unmeasured_kernel_nontrivial hκ hs h00 hsmall hγsmall RY
    X hX δ hδ hav hδT
  exact fun hinj => hne (hinj he)

theorem coefficientCongruence_ne_bot [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin 1 → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (X : GammaGroundRESObject hc B 0) (hX : Nonempty X.obj.domain)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ)
    (hav : GammaGroundRESAvailableValueTuple X (fun _ : Fin 1 => δ))
    (hδT : δ * δ ∉ translationSubgroup hc B) :
    gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B) ≠ ⊥ := by
  intro hbot
  obtain ⟨hpair, _, hne⟩ := proposition_3_18_unmeasured_kernel_nontrivial hκ hs h00 hsmall hγsmall RY
    X hX δ hδ hav hδT
  have hrel : gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B) (pairLeft X) (pairRight X δ hδ) :=
    RingConGen.Rel.of _ _ hpair
  rw [hbot] at hrel
  exact hne hrel

end DiamondIntegral.Section4.Proposition318Witness
