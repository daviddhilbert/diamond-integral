import «section 2».GammaTupleAutomorphisms
import Section3.TupleCompactness
import Section4.GammaPredicates
import CanonicalCountable
import «section 2».RVBoundCoordinates

/-! Γ is stably embedded, with the induced structure of a divisible ordered
abelian group.

`gamma_stably_embedded`: let `P` be a small set of parameters of the monster
model and `X ⊆ Γ^k` a set whose RV-code preimage is definable over `P`. Then
`X` is a finite Boolean combination of half-spaces `{z : ∏ zᵢ^{mᵢ} ≤ δ}`
(`m ∈ ℤ^k`) with constants `δ` among the values of the substructure generated
by `P`. In particular `X` is definable with parameters from Γ alone, in the
pure ordered-group language.

Proof. Tuples whose values have the same ℤ-type over those values are
conjugate by an automorphism fixing `P` (`exists_automorphism_code_tuple`),
so `X` is a union of such types. Saturation, through the finite subcover
lemma for definable tuple sets, then cuts each type down to a finite
intersection of half-spaces and their complements contained in `X`, and `X`
down to finitely many of these. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2.GammaStable
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
set_option linter.unusedSectionVars false

/-! ### Product-of-powers terms -/

def rvOneTerm {α : Type} : LRV.Term α := Term.func (Fn.rvOne : LRV.Functions 0) (fun i => i.elim0)
def rvZeroTerm {α : Type} : LRV.Term α := Term.func (Fn.rvZero : LRV.Functions 0) (fun i => i.elim0)
def rvMulTerm {α : Type} (t s : LRV.Term α) : LRV.Term α := Term.func (Fn.rvMul : LRV.Functions 2) ![t,s]
def rvInvTerm {α : Type} (t : LRV.Term α) : LRV.Term α := Term.func (Fn.rvInv : LRV.Functions 1) ![t]

def powTerm {α : Type} (t : LRV.Term α) : ℕ → LRV.Term α
  | 0 => rvOneTerm
  | n+1 => rvMulTerm (powTerm t n) t

def zpowTerm {α : Type} (t : LRV.Term α) : ℤ → LRV.Term α
  | Int.ofNat n => powTerm t n
  | Int.negSucc n => powTerm (rvInvTerm t) (n+1)

def prodTerm {α : Type} : (k : ℕ) → (Fin k → LRV.Term α) → (Fin k → ℤ) → LRV.Term α
  | 0, _, _ => rvOneTerm
  | k+1, ts, m => rvMulTerm (zpowTerm (ts 0) (m 0)) (prodTerm k (fun i => ts i.succ) (fun i => m i.succ))

theorem realize_rvOneTerm {α : Type} (v : α → M) : (rvOneTerm : LRV.Term α).realize v = (1 : RVS M).val := by
  rw [RVOperations.one_val]
  change Structure.funMap (L := LRV) Fn.rvOne _ = Structure.funMap (L := LRV) Fn.rvOne _
  congr 1
  funext i
  exact i.elim0

theorem realize_rvMulTerm {α : Type} (v : α → M) (t s : LRV.Term α) :
    (rvMulTerm t s).realize v = iRVMul (t.realize v) (s.realize v) := by
  change Structure.funMap (L := LRV) Fn.rvMul _ = _
  rw [funMap_two]
  rfl

theorem realize_rvInvTerm {α : Type} (v : α → M) (t : LRV.Term α) :
    (rvInvTerm t).realize v = iRVInvFn (t.realize v) := by
  change Structure.funMap (L := LRV) Fn.rvInv _ = _
  rw [funMap_one]
  rfl

theorem realize_powTerm {α : Type} (v : α → M) (t : LRV.Term α) (a : RVS M)
    (ha : t.realize v = a.val) (n : ℕ) : (powTerm t n).realize v = (a ^ n).val := by
  induction n with
  | zero => rw [pow_zero]; exact realize_rvOneTerm v
  | succ n ih =>
    change (rvMulTerm (powTerm t n) t).realize v = _
    rw [realize_rvMulTerm,ih,ha,← RVOperations.mul_val,pow_succ]

theorem realize_zpowTerm {α : Type} (v : α → M) (t : LRV.Term α) (a : RVS M)
    (ha : t.realize v = a.val) (m : ℤ) : (zpowTerm t m).realize v = (a ^ m).val := by
  cases m with
  | ofNat n =>
    change (powTerm t n).realize v = _
    rw [realize_powTerm v t a ha n,Int.ofNat_eq_natCast,zpow_natCast]
  | negSucc n =>
    change (powTerm (rvInvTerm t) (n+1)).realize v = _
    have hinv : (rvInvTerm t).realize v = (a⁻¹).val := by
      rw [realize_rvInvTerm,ha,RVOperations.inv_val]
    rw [realize_powTerm v (rvInvTerm t) a⁻¹ hinv (n+1),zpow_negSucc,inv_pow]

theorem realize_prodTerm {α : Type} (v : α → M) :
    ∀ (k : ℕ) (ts : Fin k → LRV.Term α) (m : Fin k → ℤ) (A : Fin k → RVS M),
      (∀ i, (ts i).realize v = (A i).val) → (prodTerm k ts m).realize v = (∏ i, A i ^ m i).val := by
  intro k
  induction k with
  | zero =>
    intro ts m A _
    rw [Finset.univ_eq_empty,Finset.prod_empty]
    exact realize_rvOneTerm v
  | succ k ih =>
    intro ts m A hA
    change (rvMulTerm (zpowTerm (ts 0) (m 0)) (prodTerm k (fun i => ts i.succ) (fun i => m i.succ))).realize v = _
    rw [realize_rvMulTerm,realize_zpowTerm v (ts 0) (A 0) (hA 0) (m 0),
      ih (fun i => ts i.succ) (fun i => m i.succ) (fun i => A i.succ) (fun i => hA i.succ),
      ← RVOperations.mul_val,Fin.prod_univ_succ]

/-! ### Codes of Γ-tuples -/

/-- The RV code tuples of the points of `X`. -/
def codeSet {k : ℕ} (X : Set (Fin k → Values.Gamma (M := M))) : Set (Fin k → M) :=
  {a | GammaSyntax.Proper a ∧ GammaSyntax.decode a ∈ X}

def properCode {k : ℕ} {a : Fin k → M} (ha : GammaSyntax.Proper a) (i : Fin k) : RVS M := ⟨a i,(ha i).1⟩

theorem properCode_ne_zero {k : ℕ} {a : Fin k → M} (ha : GammaSyntax.Proper a) (i : Fin k) :
    properCode ha i ≠ 0 := by
  intro h
  apply (ha i).2
  have h' := congrArg Subtype.val h
  rw [RVOperations.zero_val] at h'
  exact h'

theorem decode_val {k : ℕ} {a : Fin k → M} (ha : GammaSyntax.Proper a) (i : Fin k) :
    (GammaSyntax.decode a i).val = Values.vrv (properCode ha i) := by
  have h0 : properCode ha i ≠ rvZero M := by
    intro h
    exact properCode_ne_zero ha i (h.trans (Subtype.ext RVOperations.zero_val.symm))
  exact nonzero_rv_codeValue_val (properCode ha i) h0

theorem decode_prod_val {k : ℕ} {a : Fin k → M} (ha : GammaSyntax.Proper a) (m : Fin k → ℤ) :
    (∏ i, GammaSyntax.decode a i ^ m i).val = Values.vrv (∏ i, properCode ha i ^ m i) := by
  change Values.gammaValHom _ = RVOperations.vrvHom _
  rw [map_prod,map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [map_zpow,map_zpow₀]
  change (GammaSyntax.decode a i).val ^ m i = Values.vrv (properCode ha i) ^ m i
  rw [decode_val]

theorem exists_code (γ : Values.Gamma (M := M)) : ∃ t : RVS M, t ≠ 0 ∧ Values.vrv t = γ.val := by
  obtain ⟨t,ht⟩ := Values.vrv_surjective γ.val
  refine ⟨t,?_,ht⟩
  intro h0
  rw [h0,(vrv_eq_zero_iff (0 : RVS M)).mpr rfl] at ht
  exact γ.property (ht.symm.trans Values.infinity_eq_zero.symm)

theorem exists_code_tuple {k : ℕ} (z : Fin k → Values.Gamma (M := M)) :
    ∃ a : Fin k → M, GammaSyntax.Proper a ∧ GammaSyntax.decode a = z := by
  choose t ht0 ht using fun i => exists_code (z i)
  have hp : GammaSyntax.Proper (fun i => (t i).val) := by
    intro i
    refine ⟨(t i).property,fun he => ht0 i (Subtype.ext (he.trans RVOperations.zero_val.symm))⟩
  refine ⟨fun i => (t i).val,hp,funext (fun i => Subtype.ext ?_)⟩
  rw [decode_val hp i]
  exact ht i

/-! ### Definability of half-space codes -/

theorem unaryNonzeroRV_definable (A : Set M) :
    A.Definable LRV {z : Fin 1 → M | GammaParameters.NonzeroRV (z 0)} := by
  refine Set.definable_iff_exists_formula_sum.mpr
    ⟨(Relations.formula₁ (Rel.memRV : LRV.Relations 1) (Term.var (Sum.inr (0 : Fin 1))) ⊓
      ∼(Term.equal (Term.var (Sum.inr (0 : Fin 1))) rvZeroTerm) : LRV.Formula (A ⊕ Fin 1)),?_⟩
  ext z
  rw [Set.mem_setOf_eq,Set.mem_setOf_eq,Formula.realize_inf,Formula.realize_not]
  refine and_congr ?_ (not_congr ?_)
  · change iRV (z 0) ↔ Structure.RelMap (L := LRV) (M := M) Rel.memRV _
    rw [relMap_one (M := M) Rel.memRV]
    rfl
  · have hz : (rvZeroTerm : LRV.Term (A ⊕ Fin 1)).realize (Sum.elim Subtype.val z) = iRVZero := by
      change Structure.funMap (L := LRV) (M := M) Fn.rvZero _ = Structure.funMap (L := LRV) (M := M) Fn.rvZero _
      congr 1
      funext i
      exact i.elim0
    rw [Formula.realize_equal,hz]
    rfl

theorem proper_definable_raw (A : Set M) (k : ℕ) :
    A.Definable LRV {a : Fin k → M | GammaSyntax.Proper a} := by
  have h (i : Fin k) := (unaryNonzeroRV_definable (M := M) A).preimage_comp (fun _ : Fin 1 => i)
  convert Set.definable_iInter_of_finite h using 1
  ext a
  simp only [Set.mem_setOf_eq,Set.mem_iInter,Set.mem_preimage,Function.comp_apply]
  rfl

theorem halfspaceLe_definable (A : Set M) {k : ℕ} (m : Fin k → ℤ) (c : M) (hc : c ∈ A) :
    A.Definable LRV {a : Fin k → M |
      iLe ((prodTerm k (fun i => Term.var (Sum.inr i)) m : LRV.Term (A ⊕ Fin k)).realize
        (Sum.elim Subtype.val a)) c} := by
  refine Set.definable_iff_exists_formula_sum.mpr
    ⟨(Relations.formula₂ (Rel.rvLe : LRV.Relations 2) (prodTerm k (fun i => Term.var (Sum.inr i)) m)
      (Term.var (Sum.inl ⟨c,hc⟩)) : LRV.Formula (A ⊕ Fin k)),?_⟩
  ext a
  change iLe _ c ↔ Structure.RelMap (L := LRV) Rel.rvLe _
  rw [relMap_two (M := M) Rel.rvLe]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Term.realize_relabel,
    Sum.elim_comp_inl]
  rfl

/-- Codes of a half-space with a constant from `K`. -/
theorem codeSet_halfspace_eq {k : ℕ} (A : Set M) (m : Fin k → ℤ) (c : RVS M) :
    codeSet {z : Fin k → Values.Gamma (M := M) | (∏ i, z i ^ m i).val ≤ Values.vrv c} =
      {a | GammaSyntax.Proper a} ∩ {a : Fin k → M |
        iLe ((prodTerm k (fun i => Term.var (Sum.inr i)) m : LRV.Term (A ⊕ Fin k)).realize
          (Sum.elim Subtype.val a)) c.val} := by
  ext a
  constructor
  · rintro ⟨ha,hX⟩
    refine ⟨ha,?_⟩
    change iLe ((prodTerm k (fun i => Term.var (Sum.inr i)) m : LRV.Term (A ⊕ Fin k)).realize
      (Sum.elim Subtype.val a)) c.val
    rw [realize_prodTerm (Sum.elim Subtype.val a) k (fun i => Term.var (Sum.inr i)) m (properCode ha)
      (fun i => rfl),← Values.vrv_le_iff]
    change (∏ i, GammaSyntax.decode a i ^ m i).val ≤ Values.vrv c at hX
    rwa [decode_prod_val ha m] at hX
  · rintro ⟨ha,hX⟩
    refine ⟨ha,?_⟩
    change iLe ((prodTerm k (fun i => Term.var (Sum.inr i)) m : LRV.Term (A ⊕ Fin k)).realize
      (Sum.elim Subtype.val a)) c.val at hX
    rw [realize_prodTerm (Sum.elim Subtype.val a) k (fun i => Term.var (Sum.inr i)) m (properCode ha)
      (fun i => rfl),← Values.vrv_le_iff] at hX
    change (∏ i, GammaSyntax.decode a i ^ m i).val ≤ Values.vrv c
    rwa [decode_prod_val ha m]

theorem codeSet_halfspace_definable {k : ℕ} (A : Set M) (m : Fin k → ℤ) (c : RVS M) (hc : c.val ∈ A) :
    A.Definable LRV (codeSet {z : Fin k → Values.Gamma (M := M) | (∏ i, z i ^ m i).val ≤ Values.vrv c}) := by
  rw [codeSet_halfspace_eq A m c]
  exact (proper_definable_raw A k).inter (halfspaceLe_definable A m c.val hc)

theorem codeSet_compl {k : ℕ} (X : Set (Fin k → Values.Gamma (M := M))) :
    codeSet Xᶜ = {a | GammaSyntax.Proper a} \ codeSet X := by
  ext a
  simp only [codeSet,Set.mem_setOf_eq,Set.mem_compl_iff,Set.mem_diff]
  tauto

theorem codeSet_inter {k : ℕ} (X Y : Set (Fin k → Values.Gamma (M := M))) :
    codeSet (X ∩ Y) = codeSet X ∩ codeSet Y := by
  ext a
  simp only [codeSet,Set.mem_setOf_eq,Set.mem_inter_iff]
  tauto

theorem codeSet_univ {k : ℕ} : codeSet (Set.univ : Set (Fin k → Values.Gamma (M := M))) =
    {a | GammaSyntax.Proper a} := by
  ext a
  simp only [codeSet,Set.mem_setOf_eq,Set.mem_univ,and_true]

/-! ### Half-space Boolean combinations -/

/-- The values of the nonzero RV elements of `K`. -/
def substructureValues (K : LRV.Substructure M) : Set (Values.Gamma (M := M)) :=
  {δ | ∃ c : RVS M, c.val ∈ K ∧ c ≠ 0 ∧ Values.vrv c = δ.val}

/-- The Boolean algebra generated by the half-spaces `{z : ∏ zᵢ^{mᵢ} ≤ δ}` with
`δ ∈ Δ`: the sets definable in the ordered group with constants from `Δ`. -/
inductive HalfspaceBoolean {k : ℕ} (Δ : Set (Values.Gamma (M := M))) :
    Set (Fin k → Values.Gamma (M := M)) → Prop where
  | halfspace (m : Fin k → ℤ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ Δ) :
      HalfspaceBoolean Δ {z | ∏ i, z i ^ m i ≤ δ}
  | compl {X} : HalfspaceBoolean Δ X → HalfspaceBoolean Δ Xᶜ
  | inter {X Y} : HalfspaceBoolean Δ X → HalfspaceBoolean Δ Y → HalfspaceBoolean Δ (X ∩ Y)
  | univ : HalfspaceBoolean Δ Set.univ

namespace HalfspaceBoolean
variable {k : ℕ} {Δ : Set (Values.Gamma (M := M))}

theorem union {X Y : Set (Fin k → Values.Gamma (M := M))} (hX : HalfspaceBoolean Δ X)
    (hY : HalfspaceBoolean Δ Y) : HalfspaceBoolean Δ (X ∪ Y) := by
  have h := (hX.compl.inter hY.compl).compl
  rwa [← Set.compl_union,compl_compl] at h

theorem empty : HalfspaceBoolean Δ (∅ : Set (Fin k → Values.Gamma (M := M))) := by
  have h := (HalfspaceBoolean.univ (Δ := Δ) (k := k)).compl
  rwa [Set.compl_univ] at h

theorem biInter {ι : Type*} {S : Set ι} (hS : S.Finite) (f : ι → Set (Fin k → Values.Gamma (M := M)))
    (hf : ∀ i ∈ S, HalfspaceBoolean Δ (f i)) : HalfspaceBoolean Δ (⋂ i ∈ S, f i) := by
  induction S,hS using Set.Finite.induction_on with
  | empty => simpa only [Set.mem_empty_iff_false,Set.iInter_of_empty,Set.iInter_univ] using HalfspaceBoolean.univ
  | @insert a s _ _ ih =>
    rw [Set.biInter_insert]
    exact (hf a (Set.mem_insert a s)).inter (ih (fun i hi => hf i (Set.mem_insert_of_mem a hi)))

theorem biUnion {ι : Type*} {S : Set ι} (hS : S.Finite) (f : ι → Set (Fin k → Values.Gamma (M := M)))
    (hf : ∀ i ∈ S, HalfspaceBoolean Δ (f i)) : HalfspaceBoolean Δ (⋃ i ∈ S, f i) := by
  induction S,hS using Set.Finite.induction_on with
  | empty => simpa only [Set.mem_empty_iff_false,Set.iUnion_of_empty,Set.iUnion_empty] using HalfspaceBoolean.empty
  | @insert a s _ _ ih =>
    rw [Set.biUnion_insert]
    exact (hf a (Set.mem_insert a s)).union (ih (fun i hi => hf i (Set.mem_insert_of_mem a hi)))

end HalfspaceBoolean

theorem halfspace_val_eq {k : ℕ} (m : Fin k → ℤ) (c : RVS M) (hc0 : c ≠ 0) :
    ∃ δ : Values.Gamma (M := M), δ.val = Values.vrv c ∧
      {z : Fin k → Values.Gamma (M := M) | (∏ i, z i ^ m i).val ≤ Values.vrv c} =
        {z | ∏ i, z i ^ m i ≤ δ} := by
  refine ⟨⟨Values.vrv c,fun h => vrv_ne_zero hc0 (h.trans Values.infinity_eq_zero)⟩,rfl,?_⟩
  rfl

theorem HalfspaceBoolean.codeSet_definable {k : ℕ} (K : LRV.Substructure M)
    {X : Set (Fin k → Values.Gamma (M := M))} (hX : HalfspaceBoolean (substructureValues K) X) :
    (K : Set M).Definable LRV (codeSet X) := by
  induction hX with
  | halfspace m δ hδ =>
    obtain ⟨c,hcK,_,hc⟩ := hδ
    have he : {z : Fin k → Values.Gamma (M := M) | ∏ i, z i ^ m i ≤ δ} =
        {z | (∏ i, z i ^ m i).val ≤ Values.vrv c} := by
      ext z
      rw [hc]
      rfl
    rw [he]
    exact codeSet_halfspace_definable (K : Set M) m c hcK
  | compl _ ih =>
    rw [codeSet_compl]
    exact (proper_definable_raw (K : Set M) k).sdiff ih
  | inter _ _ ihX ihY =>
    rw [codeSet_inter]
    exact ihX.inter ihY
  | univ =>
    rw [codeSet_univ]
    exact proper_definable_raw (K : Set M) k

/-! ### Automorphisms preserve definable sets -/

theorem aut_mem_definable_iff (σ : M ≃[LRV] M) {P : Set M} (hσ : ∀ x ∈ P, σ x = x)
    {k : ℕ} {D : Set (Fin k → M)} (hD : P.Definable LRV D) (a : Fin k → M) :
    (fun i => σ (a i)) ∈ D ↔ a ∈ D := by
  obtain ⟨θ,hθ⟩ := raw_definable_formula_tuple hD
  have h := StrongHomClass.realize_boundedFormula σ θ (v := (Subtype.val : P → M)) (xs := a)
  have hv : (σ ∘ (Subtype.val : P → M)) = Subtype.val := funext (fun x => hσ x.val x.property)
  rw [hv] at h
  rw [← hθ,← hθ]
  exact h

/-! ### Stable embeddedness -/

theorem closure_small {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (P : Set M) (hP : Cardinal.mk P < κ) :
    Cardinal.mk (Substructure.closure LRV P : Set M) < κ := by
  have hfun : Cardinal.mk (Σ i, LRV.Functions i) ≤ Cardinal.aleph0 := by
    have : Countable (Σ i, LRV.Functions i) :=
      Function.Injective.countable (f := fun x : Σ i, LRV.Functions i => (Sum.inl x : LRV.Symbols))
        (fun x y h => Sum.inl_injective h)
    exact Cardinal.mk_le_aleph0
  have h := Substructure.lift_card_closure_le (L := LRV) (s := P)
  simp only [Cardinal.lift_id] at h
  refine h.trans_lt (max_lt hκ (Cardinal.add_lt_of_lt hκ.le hP (hfun.trans_lt hκ)))

/-- **Γ is stably embedded.** A subset of `Γ^k` definable over a small set `P`
is a finite Boolean combination of half-spaces with constants from the values
of the substructure generated by `P`. -/
theorem gamma_stably_embedded (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hh : StronglyHomogeneous M κ)
    (P : Set M) (hP : Cardinal.mk P < κ) {k : ℕ} (X : Set (Fin k → Values.Gamma (M := M)))
    (hX : P.Definable LRV (codeSet X)) :
    HalfspaceBoolean (substructureValues (Substructure.closure LRV P)) X := by
  let K := Substructure.closure LRV P
  let Δ := substructureValues K
  have hK : Cardinal.mk (K : Set M) < κ := closure_small hκ P hP
  have hPK : P ⊆ (K : Set M) := Substructure.subset_closure
  have hXK : (K : Set M).Definable LRV (codeSet X) := hX.mono hPK
  -- Basic conditions: half-spaces with constants from `K` and their complements.
  let Basic : Set (Set (Fin k → Values.Gamma (M := M))) :=
    {Y | ∃ (m : Fin k → ℤ) (c : RVS M), c.val ∈ K ∧ c ≠ 0 ∧
      (Y = {z | (∏ i, z i ^ m i).val ≤ Values.vrv c} ∨ Y = {z | (∏ i, z i ^ m i).val ≤ Values.vrv c}ᶜ)}
  have hBasicHB : ∀ Y ∈ Basic, HalfspaceBoolean Δ Y := by
    rintro Y ⟨m,c,hcK,hc0,hY | hY⟩
    · obtain ⟨δ,hδ,he⟩ := halfspace_val_eq m c hc0
      rw [hY,he]
      exact .halfspace m δ (show δ ∈ substructureValues K from ⟨c,hcK,hc0,hδ.symm⟩)
    · obtain ⟨δ,hδ,he⟩ := halfspace_val_eq m c hc0
      rw [hY,he]
      exact (HalfspaceBoolean.halfspace m δ (show δ ∈ substructureValues K from ⟨c,hcK,hc0,hδ.symm⟩)).compl
  -- Claim 1: every point of `X` lies in a finite intersection of basic
  -- conditions contained in `X`.
  have hcell : ∀ γ ∈ X, ∃ Y : Set (Fin k → Values.Gamma (M := M)),
      HalfspaceBoolean Δ Y ∧ γ ∈ Y ∧ Y ⊆ X := by
    intro γ hγ
    let C : Set (Set (Fin k → M)) := {codeSet X} ∪ (fun Y => codeSet Yᶜ) '' {Y | Y ∈ Basic ∧ γ ∈ Y}
    have hCdef : ∀ D ∈ C, (K : Set M).Definable LRV D := by
      rintro D (hD | ⟨Y,⟨hYB,_⟩,rfl⟩)
      · rw [Set.mem_singleton_iff.mp hD]
        exact hXK
      · exact HalfspaceBoolean.codeSet_definable K (hBasicHB Y hYB).compl
    have hcov : ∀ a ∈ {a : Fin k → M | GammaSyntax.Proper a}, ∃ D ∈ C, a ∈ D := by
      intro a ha
      by_cases haX : GammaSyntax.decode a ∈ X
      · exact ⟨codeSet X,Or.inl rfl,ha,haX⟩
      by_contra hno
      simp only [not_exists,not_and] at hno
      apply haX
      -- `decode a` satisfies every basic condition true at `γ`.
      have hall : ∀ Y ∈ Basic, γ ∈ Y → GammaSyntax.decode a ∈ Y := by
        intro Y hYB hγY
        by_contra haY
        exact hno _ (Or.inr ⟨Y,⟨hYB,hγY⟩,rfl⟩) (show a ∈ codeSet Yᶜ from ⟨ha,haY⟩)
      -- Codes of `γ` and of `decode a` have the same ℤ-type over `K`.
      obtain ⟨b,hb,hbγ⟩ := exists_code_tuple γ
      let T : Fin k → RVS M := properCode hb
      let T' : Fin k → RVS M := properCode ha
      have hType : CodeTupleTypeEq K T T' := by
        intro m c hcK hc0
        let H : Set (Fin k → Values.Gamma (M := M)) := {z | (∏ i, z i ^ m i).val ≤ Values.vrv c}
        have hTγ : Values.vrv (∏ i, T i ^ m i) ≤ Values.vrv c ↔ γ ∈ H := by
          change _ ↔ (∏ i, γ i ^ m i).val ≤ Values.vrv c
          rw [← hbγ,decode_prod_val hb m]
        have hTa : Values.vrv (∏ i, T' i ^ m i) ≤ Values.vrv c ↔ GammaSyntax.decode a ∈ H := by
          change _ ↔ (∏ i, GammaSyntax.decode a i ^ m i).val ≤ Values.vrv c
          rw [decode_prod_val ha m]
        rw [hTγ,hTa]
        constructor
        · intro hγH
          exact hall H ⟨m,c,hcK,hc0,Or.inl rfl⟩ hγH
        · intro haH
          by_contra hγH
          exact hall Hᶜ ⟨m,c,hcK,hc0,Or.inr rfl⟩ hγH haH
      obtain ⟨σ,hσK,hσ⟩ := exists_automorphism_code_tuple hc hκ hh k K hK T T'
        (properCode_ne_zero hb) (properCode_ne_zero ha) hType
      have hbX : b ∈ codeSet X := ⟨hb,hbγ ▸ hγ⟩
      have hσb := (aut_mem_definable_iff σ (fun x hx => hσK x (hPK hx)) hX b).mpr hbX
      obtain ⟨hσbp,hσbX⟩ := hσb
      have hdec : GammaSyntax.decode (fun i => σ (b i)) = GammaSyntax.decode a := by
        funext i
        apply Subtype.ext
        rw [decode_val hσbp i,decode_val ha i]
        exact hσ i (T i) rfl
      rwa [hdec] at hσbX
    obtain ⟨C₀,hC₀fin,hC₀C,hC₀cov⟩ := hs.definable_finite_subcover_tuple (K : Set M) hK
      {a | GammaSyntax.Proper a} (proper_definable_raw (K : Set M) k) C hCdef hcov
    -- Choose the basic condition behind each member of `C₀`.
    have hchoose : ∀ D ∈ C₀, D = codeSet X ∨ ∃ Y, Y ∈ Basic ∧ γ ∈ Y ∧ D = codeSet Yᶜ := by
      intro D hD
      rcases hC₀C hD with h | ⟨Y,⟨hYB,hγY⟩,rfl⟩
      · exact Or.inl (Set.mem_singleton_iff.mp h)
      · exact Or.inr ⟨Y,hYB,hγY,rfl⟩
    let pick (D : Set (Fin k → M)) : Set (Fin k → Values.Gamma (M := M)) :=
      if h : ∃ Y, Y ∈ Basic ∧ γ ∈ Y ∧ D = codeSet Yᶜ then Classical.choose h else Set.univ
    have hpick (D : Set (Fin k → M)) (hDC : D ∈ C₀) : HalfspaceBoolean Δ (pick D) ∧ γ ∈ pick D ∧
        (∀ z, z ∈ pick D → ∀ a, GammaSyntax.Proper a → GammaSyntax.decode a = z → a ∉ D ∨ D = codeSet X) := by
      by_cases h : ∃ Y, Y ∈ Basic ∧ γ ∈ Y ∧ D = codeSet Yᶜ
      · have hs := Classical.choose_spec h
        simp only [pick,dif_pos h]
        refine ⟨hBasicHB _ hs.1,hs.2.1,fun z hz a ha hdz => Or.inl ?_⟩
        rw [hs.2.2]
        rintro ⟨_,hnot⟩
        rw [hdz] at hnot
        exact hnot hz
      · simp only [pick,dif_neg h]
        refine ⟨.univ,Set.mem_univ γ,fun z _ a _ _ => ?_⟩
        by_cases hD : D = codeSet X
        · exact Or.inr hD
        · left
          intro haD
          exact h (by
            rcases hchoose D hDC with h1 | h1
            · exact absurd h1 hD
            · exact h1)
    refine ⟨⋂ D ∈ C₀, pick D,HalfspaceBoolean.biInter hC₀fin pick (fun D hD => (hpick D hD).1),
      Set.mem_iInter₂.mpr (fun D hD => (hpick D hD).2.1),?_⟩
    intro z hz
    obtain ⟨a,ha,haz⟩ := exists_code_tuple z
    obtain ⟨D,hD,haD⟩ := hC₀cov a ha
    rcases (hpick D hD).2.2 z (Set.mem_iInter₂.mp hz D hD) a ha haz with hnot | hDX
    · exact absurd haD hnot
    · rw [hDX] at haD
      rw [← haz]
      exact haD.2
  -- Claim 2: finitely many cells cover `X`.
  let C : Set (Set (Fin k → M)) := {D | ∃ Y, HalfspaceBoolean Δ Y ∧ Y ⊆ X ∧ D = codeSet Y}
  have hCdef : ∀ D ∈ C, (K : Set M).Definable LRV D := by
    rintro D ⟨Y,hY,_,rfl⟩
    exact HalfspaceBoolean.codeSet_definable K hY
  have hcov : ∀ a ∈ codeSet X, ∃ D ∈ C, a ∈ D := by
    rintro a ⟨ha,haX⟩
    obtain ⟨Y,hY,hγY,hYX⟩ := hcell _ haX
    exact ⟨codeSet Y,⟨Y,hY,hYX,rfl⟩,ha,hγY⟩
  obtain ⟨C₀,hC₀fin,hC₀C,hC₀cov⟩ := hs.definable_finite_subcover_tuple (K : Set M) hK (codeSet X) hXK C hCdef hcov
  let pick (D : Set (Fin k → M)) : Set (Fin k → Values.Gamma (M := M)) :=
    if h : ∃ Y, HalfspaceBoolean Δ Y ∧ Y ⊆ X ∧ D = codeSet Y then Classical.choose h else ∅
  have hpick (D : Set (Fin k → M)) (hD : D ∈ C₀) :
      HalfspaceBoolean Δ (pick D) ∧ pick D ⊆ X ∧ D = codeSet (pick D) := by
    have h : ∃ Y, HalfspaceBoolean Δ Y ∧ Y ⊆ X ∧ D = codeSet Y := hC₀C hD
    simp only [pick,dif_pos h]
    exact Classical.choose_spec h
  have hXeq : X = ⋃ D ∈ C₀, pick D := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨a,ha,haz⟩ := exists_code_tuple z
      obtain ⟨D,hD,haD⟩ := hC₀cov a ⟨ha,haz ▸ hz⟩
      rw [(hpick D hD).2.2] at haD
      exact Set.mem_biUnion hD (haz ▸ haD.2)
    · intro z hz
      obtain ⟨D,hD,hzD⟩ := Set.mem_iUnion₂.mp hz
      exact (hpick D hD).2.1 hzD
  rw [hXeq]
  exact HalfspaceBoolean.biUnion hC₀fin pick (fun D hD => (hpick D hD).1)

end DiamondIntegral.Section2.GammaStable
