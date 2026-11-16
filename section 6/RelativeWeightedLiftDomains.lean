import «section 6».RelativePolynomialGraphs
import Section9.WeightedLiftDomains

/-! Definable good domains for relative weighted polynomial lifts.
The complete graph imposes the inactive VF diagonal and retains the
weighted determinant condition on every point of each full fibre. -/

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open scoped BigOperators
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n d : ℕ}
local notation "VF" => VFType (M := M)

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private noncomputable def namedPolynomialTerm {E : Subfield VF} (P : MvPolynomial (Fin d) E) :
    LRV.Term (Fin P.support.card ⊕ Fin d) :=
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing (PolynomialZero.expression P))

private noncomputable def namedPolynomialArguments {E : Subfield VF}
    (P : MvPolynomial (Fin d) E) (x : Fin d → M) : Fin P.support.card ⊕ Fin d → M :=
  Sum.elim (fun j => (P.coeff (PolynomialZero.enumeration P j).val).val.val) x

private noncomputable def rawPolynomialValue {E : Subfield VF}
    (P : MvPolynomial (Fin d) E) (x : Fin d → M) : M :=
  (namedPolynomialTerm P).realize (namedPolynomialArguments P x)

private theorem rawPolynomialValue_definable {E : Subfield VF} {S : Set M}
    (hE : ∀ c : E, c.val.val ∈ S) (P : MvPolynomial (Fin d) E) :
    S.DefinableFun LRV (rawPolynomialValue P) := by
  have harg : S.DefinableMap LRV (namedPolynomialArguments P) := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (hE (P.coeff (PolynomialZero.enumeration P i).val))
    · exact Set.DefinableFun.proj LRV
  change S.DefinableFun LRV ((namedPolynomialTerm P).realize ∘ namedPolynomialArguments P)
  exact Set.DefinableFun.comp (g := namedPolynomialArguments P) harg
    ((namedPolynomialTerm P).definableFun_realize.mono (Set.empty_subset S))

set_option backward.isDefEq.respectTransparency false in
private theorem rawPolynomialValue_realizes {E : Subfield VF}
    (P : MvPolynomial (Fin d) E) (x : Fin d → VF) :
    rawPolynomialValue P (rawVF x) = ((P.map E.subtype).eval x).val := by
  let y : Fin P.support.card ⊕ Fin d → VF :=
    Sum.elim (fun j => (P.coeff (PolynomialZero.enumeration P j).val).val) x
  have hy : namedPolynomialArguments P (rawVF x) = fun i => (y i).val := by
    funext i
    cases i <;> rfl
  rw [rawPolynomialValue, hy, namedPolynomialTerm, RingSyntax.realizes,
    FirstOrder.Ring.realize_termOfFreeCommRing, eval_map]
  exact congrArg Subtype.val (PolynomialZero.expression_eval P E.subtype x)

private noncomputable def blockProduct {E : Subfield VF}
    (H : Fin n → MvPolynomial (Fin (n + n)) E) (f : Fin n ↪ Fin (n + n)) :
    MvPolynomial (Fin (n + n)) E :=
  partialJacobianPolynomial f H * ∏ j, X (f j)

private theorem blockProduct_realizes {E : Subfield VF}
    (H : Fin n → MvPolynomial (Fin (n + n)) E) (f : Fin n ↪ Fin (n + n))
    (x : Fin (n + n) → VF) :
    ((blockProduct H f).map E.subtype).eval x =
      (partialJacobianPolynomial f (fun i => (H i).map E.subtype)).eval x * ∏ j, x (f j) := by
  have hmap : (partialJacobianPolynomial f H).map E.subtype =
      partialJacobianPolynomial f (fun i => (H i).map E.subtype) := by
    rw [partialJacobianPolynomial, RingHom.map_det, partialJacobianPolynomial]
    congr 1
    apply Matrix.ext
    intro i j
    change ((pderiv (f j)) (H i)).map E.subtype = (pderiv (f j)) ((H i).map E.subtype)
    rw [pderiv_map]
  rw [blockProduct, map_mul, map_prod, hmap]
  simp only [MvPolynomial.map_X E.subtype,(MvPolynomial.eval x).map_mul,
    MvPolynomial.eval_prod,MvPolynomial.eval_X]
  rfl

private def hasWeightedBlocks {E : Subfield VF} (H : Fin n → MvPolynomial (Fin (n + n)) E)
    (x : Fin (n + n) → M) : Prop :=
  let a := rawPolynomialValue (blockProduct H (productLeft n n)) x
  let b := rawPolynomialValue (blockProduct H (productRight n n)) x
  b ≠ iVFZero ∧ iLe (iRv a) (iRv b) ∧ iLe (iRv b) (iRv a)

private theorem hasWeightedBlocks_definable {E : Subfield VF} {S : Set M}
    (hE : ∀ c : E, c.val.val ∈ S) (H : Fin n → MvPolynomial (Fin (n + n)) E) :
    S.Definable LRV {x | hasWeightedBlocks H x} := by
  let P := blockProduct H (productLeft n n)
  let Q := blockProduct H (productRight n n)
  have hzero : S.DefinableFun LRV (fun _ : Fin (n + n) → M => iVFZero) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hval : S.DefinableMap LRV (fun x : Fin (n + n) → M =>
      ![rawPolynomialValue P x, rawPolynomialValue Q x]) := by
    intro i
    fin_cases i
    · exact rawPolynomialValue_definable hE P
    · exact rawPolynomialValue_definable hE Q
  have he := (termValueEq_definable S (.var (0 : Fin 2)) (.var 1)).preimage_map hval
  have hp := ((rawPolynomialValue_definable hE Q).ofPred_eq hzero).compl
  convert hp.inter he using 1
  ext x
  change hasWeightedBlocks H x ↔ _ ∧ termValueEq _ _ _
  rw [termValueEq_realize]
  rfl

def relativeWeightedLiftDomain {E : Subfield VF} (H : Fin n → MvPolynomial (Fin (n + n)) E) (i : Fin n) :
    Set (Fin (n + n) → M) :=
  rawLiftDomain (relativePolynomialGraph H i) ∩
    {z | ∀ x ∈ relativePolynomialGraph H i, iRv ∘ x = z → hasWeightedBlocks H x}

theorem relativeWeightedLiftDomain_definable {E : Subfield VF} {S : Set M}
    (hE : ∀ c : E, c.val.val ∈ S) (H : Fin n → MvPolynomial (Fin (n + n)) E) (i : Fin n) :
    S.Definable LRV (relativeWeightedLiftDomain H i) := by
  let ι := Fin (n + n)
  have hA := relativePolynomialGraph_definable hE H i
  have heq : S.Definable LRV {w : ι ⊕ ι → M | iRv ∘ w ∘ Sum.inr = w ∘ Sum.inl} := by
    simp only [funext_iff, Set.ofPred_forall, Function.comp_apply]
    exact Set.definable_iInter_of_finite (fun i =>
      ((definable_rvTuple S (ι := ι ⊕ ι)) (.inr i)).ofPred_eq (Set.DefinableFun.proj LRV))
  have hbad := (((hA.preimage_comp (Sum.inr : ι → ι ⊕ ι)).inter heq).inter
    ((hasWeightedBlocks_definable hE H).compl.preimage_comp Sum.inr)).exists_of_finite
  convert (rawLiftDomain_definable S _ hA).inter hbad.compl using 1
  ext z
  change (z ∈ rawLiftDomain (relativePolynomialGraph H i) ∧
    (∀ x ∈ relativePolynomialGraph H i, iRv ∘ x = z → hasWeightedBlocks H x)) ↔
    z ∈ rawLiftDomain (relativePolynomialGraph H i) ∧
      ¬ ∃ x, (x ∈ relativePolynomialGraph H i ∧ iRv ∘ x = z) ∧ ¬ hasWeightedBlocks H x
  exact and_congr_right (fun _ => by push Not; tauto)

section

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (VFType (M := M)) Γ)
variable (hw : ∀ x y : VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)

include hw in
private theorem hasWeightedBlocks_iff {E : Subfield VF}
    (H : Fin n → MvPolynomial (Fin (n + n)) E) (x : Fin (n + n) → VF) :
    hasWeightedBlocks H (rawVF x) ↔
      let Z := fun i => (H i).map E.subtype
      let A := (partialJacobianPolynomial (productLeft n n) Z).eval x
      let B := (partialJacobianPolynomial (productRight n n) Z).eval x
      let left := A * ∏ j, x (productLeft n n j)
      let right := B * ∏ j, x (productRight n n j)
      right ≠ 0 ∧ w left = w right := by
  simp only [hasWeightedBlocks, rawPolynomialValue_realizes, blockProduct_realizes]
  refine and_congr ?_ ⟨fun h =>
    le_antisymm ((hw _ _).mp h.2) ((hw _ _).mp h.1),
    fun h => ⟨(hw _ _).mpr h.ge, (hw _ _).mpr h.le⟩⟩
  change (_ : VF).val ≠ (0 : VF).val ↔ _
  exact not_congr Subtype.val_inj

theorem mem_relativeWeightedLiftDomain_of_blocks {E : Subfield VF}
    (i : Fin n) (t s : Fin n → _root_.RVCalc.RV w) (ht : ∀ i, t i ≠ none) (hs : ∀ i, s i ≠ none)
    (H : Fin n → MvPolynomial (Fin (n + n)) E) (α : Fin n → Γ)
    (hH : let u := productTuple t s
      let Z := fun i => (H i).map E.subtype
      (∀ i, IsGammaPolynomial w (fun j => _root_.RVCalc.vrv w (u j)) (α i) (Z i)) ∧
      ¬ IsResidueRoot w u (jacobianValue (fun j => _root_.RVCalc.vrv w (t j)) α)
        (partialJacobianPolynomial (productLeft n n) Z) ∧
      ¬ IsResidueRoot w u (jacobianValue (fun j => _root_.RVCalc.vrv w (s j)) α)
        (partialJacobianPolynomial (productRight n n) Z) ∧
      FibreBijection w {p | ∀ i, (Z i).eval (productTuple p.1 p.2) = 0} t s)
    (hFixed : ∀ a ∈ RVFibre w t,∀ b ∈ RVFibre w s,
      (∀ j,((H j).map E.subtype).eval (productTuple a b) = 0) → ∀ j,j ≠ i → b j = a j) :
    productTuple (rawRV w hw t) (rawRV w hw s) ∈ relativeWeightedLiftDomain H i := by
  let u := productTuple t s
  let Z := fun i => (H i).map E.subtype
  have hu (j : Fin (n + n)) : u j ≠ none := by
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
    cases i with
    | inl i =>
      change u (productLeft n n i) ≠ none
      simpa only [u, productTuple_left] using ht i
    | inr i =>
      change u (productRight n n i) ≠ none
      simpa only [u, productTuple_right] using hs i
  refine ⟨?_, fun x hx he => ?_⟩
  · apply (rawLiftDomain_mem_iff w hw (relativePolynomialGraph H i) t s).mpr
    exact relativePolynomialGraph_fibreBijection w H i t s hH.2.2.2 hFixed
  · let a : Fin (n+n) → VF := fun j => ⟨x j,relativePolynomialGraph_vf H i x hx j⟩
    have ha : a ∈ RVFibre w u := by
      intro j
      apply (CanonicalRV.equiv w hw).injective
      apply Subtype.ext
      rw [CanonicalRV.equiv_rv]
      have hj := congrFun he j
      have hcode : productTuple (rawRV w hw t) (rawRV w hw s) j =
          (CanonicalRV.equiv w hw (u j)).val := by
        obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
        cases i with
        | inl i =>
          change productTuple (rawRV w hw t) (rawRV w hw s) (productLeft n n i) =
            (CanonicalRV.equiv w hw (u (productLeft n n i))).val
          simp only [u, productTuple_left, rawRV]
        | inr i =>
          change productTuple (rawRV w hw t) (rawRV w hw s) (productRight n n i) =
            (CanonicalRV.equiv w hw (u (productRight n n i))).val
          simp only [u, productTuple_right, rawRV]
      exact hj.trans hcode
    have hleft := weightedBlock_value_mul_columns w u hu Z hH.1 (productLeft n n)
      (by simpa only [u, productTuple_left] using hH.2.1) ha
    have hright := weightedBlock_value_mul_columns w u hu Z hH.1 (productRight n n)
      (by simpa only [u, productTuple_right] using hH.2.2.1) ha
    apply (hasWeightedBlocks_iff w hw H a).mpr
    exact ⟨w.ne_zero_iff.mp (hright.trans_ne
      (Finset.prod_ne_zero_iff.mpr fun i _ => (hH.1 i).2.1)), hleft.trans hright.symm⟩

theorem relativeWeightedLiftDomain_blocks {E : Subfield VF}
    (H : Fin n → MvPolynomial (Fin (n+n)) E) (i : Fin n)
    (t s : Fin n → _root_.RVCalc.RV w)
    (hD : productTuple (rawRV w hw t) (rawRV w hw s) ∈ relativeWeightedLiftDomain H i)
    (a : Fin n → VF) (ha : a ∈ RVFibre w t) (b : Fin n → VF) (hb : b ∈ RVFibre w s)
    (hGraph : productTuple (rawVF a) (rawVF b) ∈ relativePolynomialGraph H i) :
    let W := fun j => (H j).map E.subtype
    let x := productTuple a b
    let A := (partialJacobianPolynomial (productLeft n n) W).eval x * ∏ j,a j
    let D := (partialJacobianPolynomial (productRight n n) W).eval x * ∏ j,b j
    D ≠ 0 ∧ w A = w D := by
  have ha' : rawVF a ∈ rawTupleFibre
      (productTuple (rawRV w hw t) (rawRV w hw s) ∘ productLeft n n) := by
    simpa only [Function.comp_def,productTuple_left] using (rawVF_mem_rawTupleFibre_iff w hw t a).mpr ha
  have hb' : rawVF b ∈ rawTupleFibre
      (productTuple (rawRV w hw t) (rawRV w hw s) ∘ productRight n n) := by
    simpa only [Function.comp_def,productTuple_right] using (rawVF_mem_rawTupleFibre_iff w hw s b).mpr hb
  have h := hD.2 _ hGraph (productTuple_rv_of_rawTupleFibre ha' hb')
  have hRaw : productTuple (rawVF a) (rawVF b) = rawVF (productTuple a b) := by
    apply productTuple_ext
    · intro j
      rw [productTuple_left]
      change (a j).val = (productTuple a b (productLeft n n j)).val
      rw [productTuple_left]
    · intro j
      rw [productTuple_right]
      change (b j).val = (productTuple a b (productRight n n j)).val
      rw [productTuple_right]
  rw [hRaw] at h
  simpa only [productTuple_left,productTuple_right] using
    (hasWeightedBlocks_iff w hw H (productTuple a b)).mp h

end
end DiamondIntegral.Section6
