import Section3.RVOperations
import Section3.QuantifierFree
import Section3.SortedTuples
import Section3.GuardedRationalNormalForm
import Section4.HomogeneousAvoidance

/-! Stable embeddedness of Γ, the one-code step.

Let `K` be a small substructure of the monster model and `Δ` the values of
its nonzero RV elements. Let `T, T'` be nonzero RV codes such that `vrv T` and
`vrv T'` have the same ℤ-type over `Δ`:
`vrv (T^m) ≤ δ ↔ vrv (T'^m) ≤ δ` for all `m ∈ ℤ` and `δ ∈ Δ`.

If `vrv T` is ℤ-independent over `Δ`, then `VF(K) ∪ {c·T^m : c ∈ RV(K), m ∈ ℤ}`
is a substructure (`codeSubstructure`); the junk conventions of the RV
language make it closed under the residue operations. The shift
`c·T^m ↦ c·T'^m` is an isomorphism onto the corresponding substructure for
`T'` (`codeShiftEquiv`). By quantifier elimination `T` and `T'` have the same
type over `K` (`code_sameUnaryType`), so strong homogeneity gives an
automorphism fixing `K` and sending `T` to `T'`. If `vrv T` is dependent, the
two values coincide (`exists_automorphism_code`). -/

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

abbrev RVS (M : Type) [LRV.Structure M] := CanonicalRV.RVSort M

/-! ### Values in the RV group -/

theorem vrv_zpow (t : RVS M) (m : ℤ) : Values.vrv (t ^ m) = Values.vrv t ^ m :=
  map_zpow₀ RVOperations.vrvHom t m

theorem vrv_eq_zero_iff (t : RVS M) : Values.vrv t = 0 ↔ t = 0 := by
  rw [← Values.infinity_eq_zero,Values.vrv_eq_infinity_iff,Subtype.ext_iff,RVOperations.zero_val]

theorem vrv_ne_zero {t : RVS M} (ht : t ≠ 0) : Values.vrv t ≠ 0 :=
  fun h => ht ((vrv_eq_zero_iff t).mp h)

theorem gammaTop_mul_le_mul_iff {u a b : Values.GammaTop (M := M)} (hu : u ≠ 0) :
    u * a ≤ u * b ↔ a ≤ b := by
  constructor
  · intro h
    have h' := mul_le_mul' (le_refl u⁻¹) h
    rwa [← mul_assoc,← mul_assoc,inv_mul_cancel₀ hu,one_mul,one_mul] at h'
  · intro h
    exact mul_le_mul' (le_refl u) h

theorem gammaTop_le_zero (a : Values.GammaTop (M := M)) : a ≤ 0 :=
  Values.infinity_eq_zero (M := M) ▸ Values.le_infinity a

theorem gammaTop_zero_le_iff (a : Values.GammaTop (M := M)) : 0 ≤ a ↔ a = 0 :=
  ⟨fun h => le_antisymm (gammaTop_le_zero a) h,fun h => h ▸ le_refl _⟩

/-! ### RV elements of a substructure -/

theorem rvZero_mem (K : LRV.Substructure M) : iRVZero ∈ K :=
  K.fun_mem Fn.rvZero _ (fun i => i.elim0)

theorem rvOne_mem (K : LRV.Substructure M) : iRVOne ∈ K :=
  K.fun_mem Fn.rvOne _ (fun i => i.elim0)

theorem vfZero_mem (K : LRV.Substructure M) : iVFZero ∈ K :=
  K.fun_mem Fn.vfZero _ (fun i => i.elim0)

theorem fun1_mem (K : LRV.Substructure M) (f : Fn 1) {x : M} (hx : x ∈ K) :
    Structure.funMap (L := LRV) f ![x] ∈ K :=
  K.fun_mem f _ (fun i => by fin_cases i; exact hx)

theorem fun2_mem (K : LRV.Substructure M) (f : Fn 2) {x y : M} (hx : x ∈ K) (hy : y ∈ K) :
    Structure.funMap (L := LRV) f ![x,y] ∈ K :=
  K.fun_mem f _ (fun i => by fin_cases i; exacts [hx,hy])

theorem rv_zero_mem_K (K : LRV.Substructure M) : (0 : RVS M).val ∈ K := by
  rw [RVOperations.zero_val]
  exact rvZero_mem K

theorem rv_one_mem_K (K : LRV.Substructure M) : (1 : RVS M).val ∈ K := by
  rw [RVOperations.one_val]
  exact rvOne_mem K

theorem rv_mul_mem_K (K : LRV.Substructure M) {c c' : RVS M} (hc : c.val ∈ K) (hc' : c'.val ∈ K) :
    (c * c').val ∈ K := by
  rw [RVOperations.mul_val]
  exact fun2_mem K Fn.rvMul hc hc'

theorem rv_inv_mem_K (K : LRV.Substructure M) {c : RVS M} (hc : c.val ∈ K) : (c⁻¹).val ∈ K := by
  rw [RVOperations.inv_val]
  exact fun1_mem K Fn.rvInv hc

/-! ### Independence and ℤ-types of a code over a substructure -/

/-- `vrv T` is ℤ-independent over the values of `K`. -/
def CodeIndependent (K : LRV.Substructure M) (T : RVS M) : Prop :=
  ∀ m : ℤ, m ≠ 0 → ∀ c : RVS M, c.val ∈ K → Values.vrv (T ^ m) ≠ Values.vrv c

/-- `vrv T` and `vrv T'` have the same ℤ-type over the values of `K`. -/
def CodeTypeEq (K : LRV.Substructure M) (T T' : RVS M) : Prop :=
  ∀ m : ℤ, ∀ c : RVS M, c.val ∈ K → c ≠ 0 →
    (Values.vrv (T ^ m) ≤ Values.vrv c ↔ Values.vrv (T' ^ m) ≤ Values.vrv c)

theorem CodeTypeEq.ge {K : LRV.Substructure M} {T T' : RVS M} (h : CodeTypeEq K T T')
    (hT : T ≠ 0) (hT' : T' ≠ 0) (m : ℤ) (c : RVS M) (hc : c.val ∈ K) (hc0 : c ≠ 0) :
    Values.vrv c ≤ Values.vrv (T ^ m) ↔ Values.vrv c ≤ Values.vrv (T' ^ m) := by
  have hci := rv_inv_mem_K K hc
  have hci0 : c⁻¹ ≠ 0 := inv_ne_zero hc0
  have key (S : RVS M) (hS : S ≠ 0) :
      Values.vrv c ≤ Values.vrv (S ^ m) ↔ Values.vrv (S ^ (-m)) ≤ Values.vrv c⁻¹ := by
    have hu : Values.vrv (S ^ (-m)) * Values.vrv c⁻¹ ≠ 0 :=
      mul_ne_zero (vrv_ne_zero (zpow_ne_zero _ hS)) (vrv_ne_zero hci0)
    rw [← gammaTop_mul_le_mul_iff hu]
    have h1 : Values.vrv (S ^ (-m)) * Values.vrv c⁻¹ * Values.vrv c = Values.vrv (S ^ (-m)) := by
      rw [mul_assoc,← RVOperations.vrv_mul,inv_mul_cancel₀ hc0,RVOperations.vrv_one,mul_one]
    have h2 : Values.vrv (S ^ (-m)) * Values.vrv c⁻¹ * Values.vrv (S ^ m) = Values.vrv c⁻¹ := by
      rw [mul_comm (Values.vrv (S ^ (-m))),mul_assoc,← RVOperations.vrv_mul,← zpow_add₀ hS,
        neg_add_cancel,zpow_zero,RVOperations.vrv_one,mul_one]
    rw [h1,h2]
  rw [key T hT,key T' hT']
  exact h (-m) c⁻¹ hci hci0

theorem CodeTypeEq.eq_iff {K : LRV.Substructure M} {T T' : RVS M} (h : CodeTypeEq K T T')
    (hT : T ≠ 0) (hT' : T' ≠ 0) (m : ℤ) (c : RVS M) (hc : c.val ∈ K) (hc0 : c ≠ 0) :
    Values.vrv (T ^ m) = Values.vrv c ↔ Values.vrv (T' ^ m) = Values.vrv c := by
  rw [le_antisymm_iff,le_antisymm_iff,h m c hc hc0,h.ge hT hT' m c hc hc0]

theorem CodeTypeEq.independent {K : LRV.Substructure M} {T T' : RVS M} (h : CodeTypeEq K T T')
    (hT : T ≠ 0) (hT' : T' ≠ 0) (hind : CodeIndependent K T) : CodeIndependent K T' := by
  intro m hm c hc he
  by_cases hc0 : c = 0
  · rw [hc0,(vrv_eq_zero_iff 0).mpr rfl] at he
    exact vrv_ne_zero (zpow_ne_zero m hT') he
  · exact hind m hm c hc ((h.eq_iff hT hT' m c hc hc0).mpr he)

/-! ### Representations `c·T^m` -/

theorem rep_unique {K : LRV.Substructure M} {T : RVS M} (hT : T ≠ 0) (hind : CodeIndependent K T)
    {c c' : RVS M} {m m' : ℤ} (hc : c.val ∈ K) (hc' : c'.val ∈ K) (he : c * T ^ m = c' * T ^ m') :
    (c = 0 ∧ c' = 0) ∨ (m = m' ∧ c = c') := by
  by_cases hc0 : c = 0
  · left
    refine ⟨hc0,?_⟩
    rw [hc0,zero_mul] at he
    rcases mul_eq_zero.mp he.symm with h | h
    · exact h
    · exact absurd h (zpow_ne_zero m' hT)
  · right
    have hc'0 : c' ≠ 0 := by
      intro h0
      rw [h0,zero_mul] at he
      rcases mul_eq_zero.mp he with h | h
      · exact hc0 h
      · exact zpow_ne_zero m hT h
    have hpow : T ^ (m - m') = c' * c⁻¹ := by
      rw [zpow_sub₀ hT]
      field_simp
      calc T ^ m * c = c * T ^ m := mul_comm _ _
        _ = c' * T ^ m' := he
        _ = T ^ m' * c' := mul_comm _ _
    by_contra hne
    have hmm : m - m' ≠ 0 := by
      intro h0
      apply hne
      have hm : m = m' := by omega
      refine ⟨hm,?_⟩
      rw [hm] at he
      exact mul_right_cancel₀ (zpow_ne_zero m' hT) he
    exact hind (m - m') hmm (c' * c⁻¹) (rv_mul_mem_K K hc' (rv_inv_mem_K K hc)) (by rw [hpow])

/-! ### The code substructure -/

/-- `VF(K) ∪ {c·T^m : c ∈ RV(K), m ∈ ℤ}`. -/
def codeCarrier (K : LRV.Substructure M) (T : RVS M) : Set M :=
  {x | (iVF x ∧ x ∈ K) ∨ ∃ c : RVS M, ∃ m : ℤ, c.val ∈ K ∧ x = (c * T ^ m).val}

theorem mem_codeCarrier_of_mem {K : LRV.Substructure M} {T : RVS M} {x : M} (hx : x ∈ K) :
    x ∈ codeCarrier K T := by
  rcases TypedModelMap.sort_cover x with hvf | hrv
  · exact Or.inl ⟨hvf,hx⟩
  · exact Or.inr ⟨⟨x,hrv⟩,0,hx,by rw [zpow_zero,mul_one]⟩

theorem codeCarrier_vf {K : LRV.Substructure M} {T : RVS M} {x : M} (hx : x ∈ codeCarrier K T)
    (hvf : iVF x) : x ∈ K := by
  rcases hx with ⟨_,h⟩ | ⟨c,m,_,rfl⟩
  · exact h
  · exact absurd (c * T ^ m).property (TypedModelMap.not_rv_of_vf hvf)

theorem codeCarrier_rep {K : LRV.Substructure M} {T : RVS M} {x : M} (hx : x ∈ codeCarrier K T)
    (hrv : iRV x) : ∃ c : RVS M, ∃ m : ℤ, c.val ∈ K ∧ x = (c * T ^ m).val := by
  rcases hx with ⟨hvf,_⟩ | h
  · exact absurd hrv (TypedModelMap.not_rv_of_vf hvf)
  · exact h

theorem rep_mem {K : LRV.Substructure M} {T : RVS M} {c : RVS M} (m : ℤ) (hc : c.val ∈ K) :
    (c * T ^ m).val ∈ codeCarrier K T := Or.inr ⟨c,m,hc,rfl⟩

theorem rep_new {K : LRV.Substructure M} {T : RVS M} {c : RVS M} {m : ℤ} (hc : c.val ∈ K)
    (hnew : (c * T ^ m).val ∉ K) : c ≠ 0 ∧ m ≠ 0 := by
  refine ⟨fun h0 => hnew ?_,fun h0 => hnew ?_⟩
  · rw [h0,zero_mul]
    exact rv_zero_mem_K K
  · rw [h0,zpow_zero,mul_one]
    exact hc

theorem units_vrv_one {z : RVS M} (hz : iUnits z.val) : z ≠ 0 ∧ Values.vrv z = 1 := by
  obtain ⟨h0,hl,hr⟩ := (GuardedRVNormalForm.units_iff_nonzero_orders z).mp hz
  refine ⟨h0,le_antisymm ?_ ?_⟩
  · rw [← RVOperations.vrv_one]
    exact (Values.vrv_le_iff z 1).mpr hl
  · rw [← RVOperations.vrv_one]
    exact (Values.vrv_le_iff 1 z).mpr hr

/-- A new element `c·T^m` (with `c ≠ 0`, `m ≠ 0`) is not in the residue field. -/
theorem rep_not_inK {K : LRV.Substructure M} {T : RVS M} (hT : T ≠ 0) (hind : CodeIndependent K T)
    {c : RVS M} {m : ℤ} (hc : c.val ∈ K) (hc0 : c ≠ 0) (hm : m ≠ 0) :
    ¬ ValuedModelMap.inK (c * T ^ m) := by
  rintro (hu | hz)
  · obtain ⟨_,h1⟩ := units_vrv_one hu
    apply hind m hm c⁻¹ (rv_inv_mem_K K hc)
    have h := h1
    rw [RVOperations.vrv_mul] at h
    have hcv : Values.vrv c * Values.vrv c⁻¹ = 1 := by
      rw [← RVOperations.vrv_mul,mul_inv_cancel₀ hc0,RVOperations.vrv_one]
    calc Values.vrv (T ^ m) = Values.vrv (T ^ m) * (Values.vrv c * Values.vrv c⁻¹) := by rw [hcv,mul_one]
      _ = (Values.vrv c * Values.vrv (T ^ m)) * Values.vrv c⁻¹ := by ac_rfl
      _ = Values.vrv c⁻¹ := by rw [h,one_mul]
  · have h0 : c * T ^ m = 0 := Subtype.ext (by
      rw [RVOperations.zero_val]
      exact congrArg Subtype.val hz)
    rcases mul_eq_zero.mp h0 with h | h
    · exact hc0 h
    · exact zpow_ne_zero m hT h

theorem funMap_two (f : Fn 2) (xs : Fin 2 → M) :
    Structure.funMap (L := LRV) f xs = Structure.funMap (L := LRV) f ![xs 0,xs 1] := by
  congr 1
  funext i
  fin_cases i <;> rfl

theorem funMap_one (f : Fn 1) (xs : Fin 1 → M) :
    Structure.funMap (L := LRV) f xs = Structure.funMap (L := LRV) f ![xs 0] := by
  congr 1
  funext i
  fin_cases i
  rfl

theorem junk_mem (hc : CanonicalStructure.IsCanonical (M := M)) (K : LRV.Substructure M) {n : ℕ}
    (f : Fn n) (xs : Fin n → M) (h : ¬ ∀ i, sortEval (Fn.argSort f i) (xs i)) :
    Structure.funMap (L := LRV) f xs ∈ K := by
  rw [hc.1 f xs h]
  cases hres : Fn.resSort f with
  | vf => exact vfZero_mem K
  | rv => exact rvZero_mem K

/-- The code carrier is closed under every function symbol. -/
theorem codeCarrier_fun_mem (hc : CanonicalStructure.IsCanonical (M := M))
    (K : LRV.Substructure M) {T : RVS M} (hT : T ≠ 0) (hind : CodeIndependent K T)
    {n : ℕ} (f : LRV.Functions n) (xs : Fin n → M) (hxs : ∀ i, xs i ∈ codeCarrier K T) :
    Structure.funMap (L := LRV) f xs ∈ codeCarrier K T := by
  by_cases hK : ∀ i, xs i ∈ K
  · exact mem_codeCarrier_of_mem (K.fun_mem f xs hK)
  simp only [not_forall] at hK
  obtain ⟨j,hj⟩ := hK
  have hjrv : iRV (xs j) := by
    rcases TypedModelMap.sort_cover (xs j) with h | h
    · exact absurd (codeCarrier_vf (hxs j) h) hj
    · exact h
  have hjunk_vf (f : Fn n) (hf : ∀ i, Fn.argSort f i = .vf) :
      Structure.funMap (L := LRV) f xs ∈ codeCarrier K T := by
    apply mem_codeCarrier_of_mem
    apply junk_mem hc K f xs
    intro hall
    have h := hall j
    rw [hf j] at h
    exact TypedModelMap.not_rv_of_vf h hjrv
  cases f with
  | vfZero => exact j.elim0
  | vfOne => exact j.elim0
  | rvOne => exact j.elim0
  | rvZero => exact j.elim0
  | vfAdd => exact hjunk_vf Fn.vfAdd (fun _ => rfl)
  | vfNeg => exact hjunk_vf Fn.vfNeg (fun _ => rfl)
  | vfMul => exact hjunk_vf Fn.vfMul (fun _ => rfl)
  | rvMap => exact hjunk_vf Fn.rvMap (fun _ => rfl)
  | rvMul =>
    by_cases hs : ∀ i, iRV (xs i)
    · obtain ⟨c,m,hc0,hx0⟩ := codeCarrier_rep (hxs 0) (hs 0)
      obtain ⟨c',m',hc1,hx1⟩ := codeCarrier_rep (hxs 1) (hs 1)
      rw [funMap_two]
      change iRVMul (xs 0) (xs 1) ∈ _
      rw [hx0,hx1,← RVOperations.mul_val]
      have he : c * T ^ m * (c' * T ^ m') = (c * c') * T ^ (m + m') := by
        rw [zpow_add₀ hT]
        ac_rfl
      rw [he]
      exact rep_mem (m + m') (rv_mul_mem_K K hc0 hc1)
    · exact mem_codeCarrier_of_mem (junk_mem hc K Fn.rvMul xs (fun h => hs (fun i => h i)))
  | rvInv =>
    obtain ⟨c,m,hc0,hx0⟩ := codeCarrier_rep (hxs 0) (by
      have hj0 : j = 0 := Subsingleton.elim _ _
      rw [← hj0]
      exact hjrv)
    rw [funMap_one]
    change iRVInvFn (xs 0) ∈ _
    rw [hx0,← RVOperations.inv_val]
    have he : (c * T ^ m)⁻¹ = c⁻¹ * T ^ (-m) := by
      rw [mul_inv,zpow_neg]
    rw [he]
    exact rep_mem (-m) (rv_inv_mem_K K hc0)
  | kAdd =>
    by_cases hs : ∀ i, iRV (xs i)
    · obtain ⟨c,m,hcK,hxj⟩ := codeCarrier_rep (hxs j) hjrv
      obtain ⟨hc0,hm⟩ := rep_new hcK (hxj ▸ hj)
      have hnot := rep_not_inK hT hind hcK hc0 hm
      apply mem_codeCarrier_of_mem
      rw [funMap_two]
      change iKAdd (xs 0) (xs 1) ∈ K
      have hz : ValuedModelMap.addK ⟨xs 0,hs 0⟩ ⟨xs 1,hs 1⟩ = ValuedModelMap.zeroRV := by
        apply ValuedModelMap.addK_junk
        have hxjS : (⟨xs j,hjrv⟩ : RVS M) = c * T ^ m := Subtype.ext hxj
        fin_cases j
        · left
          change ¬ ValuedModelMap.inK ⟨xs 0,hs 0⟩
          rwa [show (⟨xs 0,hs 0⟩ : RVS M) = c * T ^ m from hxjS]
        · right
          change ¬ ValuedModelMap.inK ⟨xs 1,hs 1⟩
          rwa [show (⟨xs 1,hs 1⟩ : RVS M) = c * T ^ m from hxjS]
      have hv := congrArg Subtype.val hz
      change iKAdd (xs 0) (xs 1) = iRVZero at hv
      rw [hv]
      exact rvZero_mem K
    · exact mem_codeCarrier_of_mem (junk_mem hc K Fn.kAdd xs (fun h => hs (fun i => h i)))
  | kNeg =>
    have hj0 : j = 0 := Subsingleton.elim _ _
    subst hj0
    obtain ⟨c,m,hcK,hx0⟩ := codeCarrier_rep (hxs 0) hjrv
    obtain ⟨hc0,hm⟩ := rep_new hcK (hx0 ▸ hj)
    have hnot := rep_not_inK hT hind hcK hc0 hm
    apply mem_codeCarrier_of_mem
    rw [funMap_one]
    have hz : ValuedModelMap.negK ⟨xs 0,hjrv⟩ = ValuedModelMap.zeroRV := by
      apply ValuedModelMap.negK_junk
      rwa [show (⟨xs 0,hjrv⟩ : RVS M) = c * T ^ m from Subtype.ext hx0]
    have hv := congrArg Subtype.val hz
    change Structure.funMap (L := LRV) Fn.kNeg ![xs 0] = iRVZero at hv
    rw [hv]
    exact rvZero_mem K

/-- The code substructure `K⟨T⟩`. -/
def codeSubstructure (hc : CanonicalStructure.IsCanonical (M := M)) (K : LRV.Substructure M)
    (T : RVS M) (hT : T ≠ 0) (hind : CodeIndependent K T) : LRV.Substructure M where
  carrier := codeCarrier K T
  fun_mem {_} f xs hxs := codeCarrier_fun_mem hc K hT hind f xs hxs

theorem le_codeSubstructure (hc : CanonicalStructure.IsCanonical (M := M)) (K : LRV.Substructure M)
    (T : RVS M) (hT : T ≠ 0) (hind : CodeIndependent K T) : K ≤ codeSubstructure hc K T hT hind :=
  fun _ hx => mem_codeCarrier_of_mem hx

theorem code_mem_codeSubstructure (hc : CanonicalStructure.IsCanonical (M := M)) (K : LRV.Substructure M)
    (T : RVS M) (hT : T ≠ 0) (hind : CodeIndependent K T) : T.val ∈ codeSubstructure hc K T hT hind := by
  refine Or.inr ⟨1,1,rv_one_mem_K K,?_⟩
  rw [zpow_one,one_mul]

end DiamondIntegral.Section2.GammaStable
