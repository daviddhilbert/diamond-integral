import «section 2».GammaCodeSubstructure

/-! Stable embeddedness of Γ, the one-code step (continued): the shift
`c·T^m ↦ c·T'^m` is an isomorphism `K⟨T⟩ ≅ K⟨T'⟩` fixing `K`; by quantifier
elimination `T` and `T'` have the same type over `K`; strong homogeneity gives
an automorphism over `K` sending the value of `T` to that of `T'`. -/

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

/-! ### The shift -/

/-- The shift `c·T^m ↦ c·T'^m`, the identity on everything else. -/
def codeShift (K : LRV.Substructure M) (T T' : RVS M) (x : M) : M :=
  if h : ∃ p : RVS M × ℤ, p.1.val ∈ K ∧ x = (p.1 * T ^ p.2).val then
    ((Classical.choose h).1 * T' ^ (Classical.choose h).2).val
  else x

theorem codeShift_rep {K : LRV.Substructure M} {T : RVS M} (T' : RVS M) (hT : T ≠ 0)
    (hind : CodeIndependent K T) {c : RVS M} (m : ℤ) (hc : c.val ∈ K) :
    codeShift K T T' (c * T ^ m).val = (c * T' ^ m).val := by
  have h : ∃ p : RVS M × ℤ, p.1.val ∈ K ∧ (c * T ^ m).val = (p.1 * T ^ p.2).val := ⟨(c,m),hc,rfl⟩
  unfold codeShift
  rw [dif_pos h]
  have hs := Classical.choose_spec h
  have he' : (Classical.choose h).1 * T ^ (Classical.choose h).2 = c * T ^ m := Subtype.ext hs.2.symm
  rcases rep_unique hT hind hs.1 hc he' with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [h1,zero_mul]
    subst h2
    rw [zero_mul]
  · rw [h1,h2]

theorem codeShift_vf (K : LRV.Substructure M) (T T' : RVS M) {x : M} (hx : iVF x) :
    codeShift K T T' x = x := by
  unfold codeShift
  rw [dif_neg]
  rintro ⟨⟨c,m⟩,_,rfl⟩
  exact TypedModelMap.not_rv_of_vf hx (c * T ^ m).property

theorem codeShift_of_mem {K : LRV.Substructure M} {T : RVS M} (T' : RVS M) (hT : T ≠ 0)
    (hind : CodeIndependent K T) {y : M} (hy : y ∈ K) : codeShift K T T' y = y := by
  rcases TypedModelMap.sort_cover y with hvf | hrv
  · exact codeShift_vf K T T' hvf
  · have he : y = ((⟨y,hrv⟩ : RVS M) * T ^ (0 : ℤ)).val := by rw [zpow_zero,mul_one]
    rw [he,codeShift_rep T' hT hind 0 hy,zpow_zero,mul_one,zpow_zero,mul_one]

theorem codeShift_code {K : LRV.Substructure M} {T : RVS M} (T' : RVS M) (hT : T ≠ 0)
    (hind : CodeIndependent K T) : codeShift K T T' T.val = T'.val := by
  have he : T.val = ((1 : RVS M) * T ^ (1 : ℤ)).val := by rw [zpow_one,one_mul]
  rw [he,codeShift_rep T' hT hind 1 (rv_one_mem_K K),zpow_one,one_mul]

theorem codeShift_mem {K : LRV.Substructure M} {T : RVS M} (T' : RVS M) (hT : T ≠ 0)
    (hind : CodeIndependent K T) {x : M} (hx : x ∈ codeCarrier K T) :
    codeShift K T T' x ∈ codeCarrier K T' := by
  rcases TypedModelMap.sort_cover x with hvf | hrv
  · rw [codeShift_vf K T T' hvf]
    exact mem_codeCarrier_of_mem (codeCarrier_vf hx hvf)
  · obtain ⟨c,m,hc,rfl⟩ := codeCarrier_rep hx hrv
    rw [codeShift_rep T' hT hind m hc]
    exact rep_mem m hc

theorem codeShift_codeShift {K : LRV.Substructure M} {T T' : RVS M} (hT : T ≠ 0) (hT' : T' ≠ 0)
    (hind : CodeIndependent K T) (hind' : CodeIndependent K T') {x : M} (hx : x ∈ codeCarrier K T) :
    codeShift K T' T (codeShift K T T' x) = x := by
  rcases TypedModelMap.sort_cover x with hvf | hrv
  · rw [codeShift_vf K T T' hvf,codeShift_vf K T' T hvf]
  · obtain ⟨c,m,hc,rfl⟩ := codeCarrier_rep hx hrv
    rw [codeShift_rep T' hT hind m hc,codeShift_rep T hT' hind' m hc]

theorem codeShift_rv_iff {K : LRV.Substructure M} {T : RVS M} (T' : RVS M) (hT : T ≠ 0)
    (hind : CodeIndependent K T) {x : M} (hx : x ∈ codeCarrier K T) :
    iRV (codeShift K T T' x) ↔ iRV x := by
  rcases TypedModelMap.sort_cover x with hvf | hrv
  · rw [codeShift_vf K T T' hvf]
  · obtain ⟨c,m,hc,rfl⟩ := codeCarrier_rep hx hrv
    rw [codeShift_rep T' hT hind m hc]
    exact ⟨fun _ => (c * T ^ m).property,fun _ => (c * T' ^ m).property⟩

theorem codeShift_vf_iff {K : LRV.Substructure M} {T : RVS M} (T' : RVS M) (hT : T ≠ 0)
    (hind : CodeIndependent K T) {x : M} (hx : x ∈ codeCarrier K T) :
    iVF (codeShift K T T' x) ↔ iVF x := by
  rcases TypedModelMap.sort_cover x with hvf | hrv
  · rw [codeShift_vf K T T' hvf]
  · have hr := (codeShift_rv_iff T' hT hind hx).mpr hrv
    exact ⟨fun h => absurd hr (TypedModelMap.not_rv_of_vf h),fun h => absurd hrv (TypedModelMap.not_rv_of_vf h)⟩

theorem sortEval_codeShift {K : LRV.Substructure M} {T : RVS M} (T' : RVS M) (hT : T ≠ 0)
    (hind : CodeIndependent K T) {x : M} (hx : x ∈ codeCarrier K T) (s : SortTag) :
    sortEval s (codeShift K T T' x) ↔ sortEval s x := by
  cases s
  · exact codeShift_vf_iff T' hT hind hx
  · exact codeShift_rv_iff T' hT hind hx

/-- The order comparison of two representations depends only on the ℤ-type. -/
theorem rep_le_iff {K : LRV.Substructure M} {T T' : RVS M} (hT : T ≠ 0) (hT' : T' ≠ 0)
    (htype : CodeTypeEq K T T') {c c' : RVS M} (m m' : ℤ) (hc : c.val ∈ K) (hc' : c'.val ∈ K) :
    Values.vrv (c * T ^ m) ≤ Values.vrv (c' * T ^ m') ↔
      Values.vrv (c * T' ^ m) ≤ Values.vrv (c' * T' ^ m') := by
  by_cases hc'0 : c' = 0
  · simp only [hc'0,zero_mul,(vrv_eq_zero_iff (0 : RVS M)).mpr rfl,gammaTop_le_zero]
  by_cases hc0 : c = 0
  · simp only [hc0,zero_mul,(vrv_eq_zero_iff (0 : RVS M)).mpr rfl,gammaTop_zero_le_iff,vrv_eq_zero_iff,
      mul_eq_zero,hc'0,zpow_ne_zero _ hT,zpow_ne_zero _ hT',or_self]
  have key (S : RVS M) (hS : S ≠ 0) :
      Values.vrv (c * S ^ m) ≤ Values.vrv (c' * S ^ m') ↔
        Values.vrv (S ^ (m - m')) ≤ Values.vrv (c' * c⁻¹) := by
    have hu : Values.vrv (c⁻¹ * S ^ (-m')) ≠ 0 :=
      vrv_ne_zero (mul_ne_zero (inv_ne_zero hc0) (zpow_ne_zero _ hS))
    rw [← gammaTop_mul_le_mul_iff hu,← RVOperations.vrv_mul,← RVOperations.vrv_mul]
    have h1 : c⁻¹ * S ^ (-m') * (c * S ^ m) = S ^ (m - m') := by
      rw [zpow_sub₀ hS,zpow_neg]
      field_simp
    have h2 : c⁻¹ * S ^ (-m') * (c' * S ^ m') = c' * c⁻¹ := by
      rw [zpow_neg]
      field_simp
    rw [h1,h2]
  rw [key T hT,key T' hT']
  exact htype (m - m') (c' * c⁻¹) (rv_mul_mem_K K hc' (rv_inv_mem_K K hc))
    (mul_ne_zero hc'0 (inv_ne_zero hc0))

/-! ### The isomorphism `K⟨T⟩ ≅ K⟨T'⟩` -/

theorem sortEval_eq_iVF (x : M) : sortEval .vf x = iVF x := rfl
theorem sortEval_eq_iRV (x : M) : sortEval .rv x = iRV x := rfl

/-- The shift commutes with every function symbol. -/
theorem codeShift_funMap (hc : CanonicalStructure.IsCanonical (M := M))
    {K : LRV.Substructure M} {T T' : RVS M} (hT : T ≠ 0) (hT' : T' ≠ 0)
    (hind : CodeIndependent K T) (hind' : CodeIndependent K T')
    {n : ℕ} (f : LRV.Functions n) (ys : Fin n → M) (hys : ∀ i, ys i ∈ codeCarrier K T) :
    codeShift K T T' (Structure.funMap (L := LRV) f ys) =
      Structure.funMap (L := LRV) f (fun i => codeShift K T T' (ys i)) := by
  by_cases hK : ∀ i, ys i ∈ K
  · rw [codeShift_of_mem T' hT hind (K.fun_mem f ys hK)]
    congr 1
    funext i
    exact (codeShift_of_mem T' hT hind (hK i)).symm
  simp only [not_forall] at hK
  obtain ⟨j,hj⟩ := hK
  have hjrv : iRV (ys j) := by
    rcases TypedModelMap.sort_cover (ys j) with h | h
    · exact absurd (codeCarrier_vf (hys j) h) hj
    · exact h
  -- Both sides are junk when the argument sorts fail.
  have hjunk (hs : ¬ ∀ i, sortEval (Fn.argSort f i) (ys i)) :
      codeShift K T T' (Structure.funMap (L := LRV) f ys) =
        Structure.funMap (L := LRV) f (fun i => codeShift K T T' (ys i)) := by
    have hs' : ¬ ∀ i, sortEval (Fn.argSort f i) (codeShift K T T' (ys i)) := by
      intro h
      exact hs (fun i => (sortEval_codeShift T' hT hind (hys i) _).mp (h i))
    rw [hc.1 f ys hs,hc.1 f _ hs']
    apply codeShift_of_mem T' hT hind
    cases Fn.resSort f
    · exact vfZero_mem K
    · exact rvZero_mem K
  have hvf_junk (hf : ∀ i, Fn.argSort f i = .vf) :
      codeShift K T T' (Structure.funMap (L := LRV) f ys) =
        Structure.funMap (L := LRV) f (fun i => codeShift K T T' (ys i)) := by
    apply hjunk
    intro hall
    have h := hall j
    rw [hf j] at h
    exact TypedModelMap.not_rv_of_vf h hjrv
  cases f with
  | vfZero => exact j.elim0
  | vfOne => exact j.elim0
  | rvOne => exact j.elim0
  | rvZero => exact j.elim0
  | vfAdd => exact hvf_junk (fun _ => rfl)
  | vfNeg => exact hvf_junk (fun _ => rfl)
  | vfMul => exact hvf_junk (fun _ => rfl)
  | rvMap => exact hvf_junk (fun _ => rfl)
  | rvMul =>
    by_cases hs : ∀ i, iRV (ys i)
    · obtain ⟨c,m,hc0,hx0⟩ := codeCarrier_rep (hys 0) (hs 0)
      obtain ⟨c',m',hc1,hx1⟩ := codeCarrier_rep (hys 1) (hs 1)
      rw [funMap_two Fn.rvMul ys,funMap_two Fn.rvMul (fun i => codeShift K T T' (ys i))]
      change codeShift K T T' (iRVMul (ys 0) (ys 1)) =
        iRVMul (codeShift K T T' (ys 0)) (codeShift K T T' (ys 1))
      rw [hx0,hx1,codeShift_rep T' hT hind m hc0,codeShift_rep T' hT hind m' hc1,
        ← RVOperations.mul_val,← RVOperations.mul_val]
      have he (S : RVS M) (hS : S ≠ 0) : c * S ^ m * (c' * S ^ m') = (c * c') * S ^ (m + m') := by
        rw [zpow_add₀ hS]
        ac_rfl
      rw [he T hT,he T' hT',codeShift_rep T' hT hind (m + m') (rv_mul_mem_K K hc0 hc1)]
    · exact hjunk (fun h => hs (fun i => h i))
  | rvInv =>
    have hj0 : j = 0 := Subsingleton.elim _ _
    subst hj0
    obtain ⟨c,m,hc0,hx0⟩ := codeCarrier_rep (hys 0) hjrv
    rw [funMap_one Fn.rvInv ys,funMap_one Fn.rvInv (fun i => codeShift K T T' (ys i))]
    change codeShift K T T' (iRVInvFn (ys 0)) = iRVInvFn (codeShift K T T' (ys 0))
    rw [hx0,codeShift_rep T' hT hind m hc0,← RVOperations.inv_val,← RVOperations.inv_val]
    have he (S : RVS M) : (c * S ^ m)⁻¹ = c⁻¹ * S ^ (-m) := by rw [mul_inv,zpow_neg]
    rw [he T,he T',codeShift_rep T' hT hind (-m) (rv_inv_mem_K K hc0)]
  | kAdd =>
    by_cases hs : ∀ i, iRV (ys i)
    · obtain ⟨c,m,hcK,hxj⟩ := codeCarrier_rep (hys j) hjrv
      obtain ⟨hc0,hm⟩ := rep_new hcK (hxj ▸ hj)
      have hnot := rep_not_inK hT hind hcK hc0 hm
      have hnot' := rep_not_inK hT' hind' hcK hc0 hm
      have hs' : ∀ i, iRV (codeShift K T T' (ys i)) :=
        fun i => (codeShift_rv_iff T' hT hind (hys i)).mpr (hs i)
      have hshift_j : (⟨codeShift K T T' (ys j),hs' j⟩ : RVS M) = c * T' ^ m := by
        apply Subtype.ext
        change codeShift K T T' (ys j) = _
        rw [hxj,codeShift_rep T' hT hind m hcK]
      have hL : Structure.funMap (L := LRV) Fn.kAdd ys = iRVZero := by
        rw [funMap_two]
        have hz : ValuedModelMap.addK ⟨ys 0,hs 0⟩ ⟨ys 1,hs 1⟩ = ValuedModelMap.zeroRV := by
          apply ValuedModelMap.addK_junk
          have hxjS : (⟨ys j,hjrv⟩ : RVS M) = c * T ^ m := Subtype.ext hxj
          fin_cases j
          · left
            rwa [show (⟨ys 0,hs 0⟩ : RVS M) = c * T ^ m from hxjS]
          · right
            rwa [show (⟨ys 1,hs 1⟩ : RVS M) = c * T ^ m from hxjS]
        exact congrArg Subtype.val hz
      have hR : Structure.funMap (L := LRV) Fn.kAdd (fun i => codeShift K T T' (ys i)) = iRVZero := by
        rw [funMap_two]
        have hz : ValuedModelMap.addK ⟨codeShift K T T' (ys 0),hs' 0⟩ ⟨codeShift K T T' (ys 1),hs' 1⟩ =
            ValuedModelMap.zeroRV := by
          apply ValuedModelMap.addK_junk
          fin_cases j
          · left
            rwa [show (⟨codeShift K T T' (ys 0),hs' 0⟩ : RVS M) = c * T' ^ m from hshift_j]
          · right
            rwa [show (⟨codeShift K T T' (ys 1),hs' 1⟩ : RVS M) = c * T' ^ m from hshift_j]
        exact congrArg Subtype.val hz
      rw [hL,hR]
      exact codeShift_of_mem T' hT hind (rvZero_mem K)
    · exact hjunk (fun h => hs (fun i => h i))
  | kNeg =>
    have hj0 : j = 0 := Subsingleton.elim _ _
    subst hj0
    obtain ⟨c,m,hcK,hx0⟩ := codeCarrier_rep (hys 0) hjrv
    obtain ⟨hc0,hm⟩ := rep_new hcK (hx0 ▸ hj)
    have hnot := rep_not_inK hT hind hcK hc0 hm
    have hnot' := rep_not_inK hT' hind' hcK hc0 hm
    have hs' : iRV (codeShift K T T' (ys 0)) := (codeShift_rv_iff T' hT hind (hys 0)).mpr hjrv
    have hL : Structure.funMap (L := LRV) Fn.kNeg ys = iRVZero := by
      rw [funMap_one]
      have hz : ValuedModelMap.negK ⟨ys 0,hjrv⟩ = ValuedModelMap.zeroRV := by
        apply ValuedModelMap.negK_junk
        rwa [show (⟨ys 0,hjrv⟩ : RVS M) = c * T ^ m from Subtype.ext hx0]
      exact congrArg Subtype.val hz
    have hR : Structure.funMap (L := LRV) Fn.kNeg (fun i => codeShift K T T' (ys i)) = iRVZero := by
      rw [funMap_one]
      have hz : ValuedModelMap.negK ⟨codeShift K T T' (ys 0),hs'⟩ = ValuedModelMap.zeroRV := by
        apply ValuedModelMap.negK_junk
        have he : (⟨codeShift K T T' (ys 0),hs'⟩ : RVS M) = c * T' ^ m := by
          apply Subtype.ext
          change codeShift K T T' (ys 0) = _
          rw [hx0,codeShift_rep T' hT hind m hcK]
        rwa [he]
      exact congrArg Subtype.val hz
    rw [hL,hR]
    exact codeShift_of_mem T' hT hind (rvZero_mem K)

theorem relMap_one (r : Rel 1) (xs : Fin 1 → M) :
    Structure.RelMap (L := LRV) r xs ↔ Structure.RelMap (L := LRV) r ![xs 0] := by
  have he : xs = ![xs 0] := by
    funext i
    fin_cases i
    rfl
  rw [← he]

theorem relMap_two (r : Rel 2) (xs : Fin 2 → M) :
    Structure.RelMap (L := LRV) r xs ↔ Structure.RelMap (L := LRV) r ![xs 0,xs 1] := by
  have he : xs = ![xs 0,xs 1] := by
    funext i
    fin_cases i <;> rfl
  rw [← he]

/-- The shift preserves every relation symbol. -/
theorem codeShift_relMap (hc : CanonicalStructure.IsCanonical (M := M))
    {K : LRV.Substructure M} {T T' : RVS M} (hT : T ≠ 0) (hT' : T' ≠ 0)
    (hind : CodeIndependent K T) (htype : CodeTypeEq K T T')
    {n : ℕ} (r : LRV.Relations n) (ys : Fin n → M) (hys : ∀ i, ys i ∈ codeCarrier K T) :
    Structure.RelMap (L := LRV) r (fun i => codeShift K T T' (ys i)) ↔ Structure.RelMap (L := LRV) r ys := by
  have hind' := htype.independent hT hT' hind
  cases r with
  | memVF =>
    rw [relMap_one Rel.memVF (fun i => codeShift K T T' (ys i)),relMap_one Rel.memVF ys]
    exact codeShift_vf_iff T' hT hind (hys 0)
  | memRV =>
    rw [relMap_one Rel.memRV (fun i => codeShift K T T' (ys i)),relMap_one Rel.memRV ys]
    exact codeShift_rv_iff T' hT hind (hys 0)
  | memUnits =>
    rw [relMap_one Rel.memUnits (fun i => codeShift K T T' (ys i)),relMap_one Rel.memUnits ys]
    change iUnits (codeShift K T T' (ys 0)) ↔ iUnits (ys 0)
    by_cases hK : ys 0 ∈ K
    · rw [codeShift_of_mem T' hT hind hK]
    rcases TypedModelMap.sort_cover (ys 0) with hvf | hrv
    · exact absurd (codeCarrier_vf (hys 0) hvf) hK
    obtain ⟨c,m,hcK,hx⟩ := codeCarrier_rep (hys 0) hrv
    obtain ⟨hc0,hm⟩ := rep_new hcK (hx ▸ hK)
    rw [hx,codeShift_rep T' hT hind m hcK]
    exact ⟨fun h => absurd (Or.inl h) (rep_not_inK hT' hind' hcK hc0 hm),
      fun h => absurd (Or.inl h) (rep_not_inK hT hind hcK hc0 hm)⟩
  | rvLe =>
    rw [relMap_two Rel.rvLe (fun i => codeShift K T T' (ys i)),relMap_two Rel.rvLe ys]
    change iLe (codeShift K T T' (ys 0)) (codeShift K T T' (ys 1)) ↔ iLe (ys 0) (ys 1)
    by_cases hs : iRV (ys 0) ∧ iRV (ys 1)
    · obtain ⟨c,m,hc0,hx0⟩ := codeCarrier_rep (hys 0) hs.1
      obtain ⟨c',m',hc1,hx1⟩ := codeCarrier_rep (hys 1) hs.2
      rw [hx0,hx1,codeShift_rep T' hT hind m hc0,codeShift_rep T' hT hind m' hc1,
        ← Values.vrv_le_iff,← Values.vrv_le_iff]
      exact (rep_le_iff hT hT' htype m m' hc0 hc1).symm
    · have hL : ¬ iLe (ys 0) (ys 1) := by
        intro h
        have h2 := hc.2 ![ys 0,ys 1]
        apply h2 _ h
        intro hall
        exact hs ⟨hall 0,hall 1⟩
      have hR : ¬ iLe (codeShift K T T' (ys 0)) (codeShift K T T' (ys 1)) := by
        intro h
        have h2 := hc.2 ![codeShift K T T' (ys 0),codeShift K T T' (ys 1)]
        apply h2 _ h
        intro hall
        exact hs ⟨(codeShift_rv_iff T' hT hind (hys 0)).mp (hall 0),
          (codeShift_rv_iff T' hT hind (hys 1)).mp (hall 1)⟩
      exact ⟨fun h => absurd h hR,fun h => absurd h hL⟩

/-- The shift isomorphism `K⟨T⟩ ≃ K⟨T'⟩`. -/
def codeShiftEquiv (hc : CanonicalStructure.IsCanonical (M := M))
    (K : LRV.Substructure M) (T T' : RVS M) (hT : T ≠ 0) (hT' : T' ≠ 0)
    (hind : CodeIndependent K T) (htype : CodeTypeEq K T T') :
    codeSubstructure hc K T hT hind ≃[LRV]
      codeSubstructure hc K T' hT' (htype.independent hT hT' hind) where
  toFun x := ⟨codeShift K T T' x.val,codeShift_mem T' hT hind x.property⟩
  invFun y := ⟨codeShift K T' T y.val,codeShift_mem T hT' (htype.independent hT hT' hind) y.property⟩
  left_inv x := Subtype.ext (codeShift_codeShift hT hT' hind (htype.independent hT hT' hind) x.property)
  right_inv y := Subtype.ext (codeShift_codeShift hT' hT (htype.independent hT hT' hind) hind y.property)
  map_fun' {n} f xs := by
    apply Subtype.ext
    exact codeShift_funMap hc hT hT' hind (htype.independent hT hT' hind) f (fun i => (xs i).val)
      (fun i => (xs i).property)
  map_rel' {n} r xs := by
    exact codeShift_relMap hc hT hT' hind htype r (fun i => (xs i).val) (fun i => (xs i).property)

/-! ### Same type over `K` -/

/-- By quantifier elimination, codes of the same ℤ-type over `K` with an
independent value have the same type over `K`. -/
theorem code_sameUnaryType (hc : CanonicalStructure.IsCanonical (M := M))
    (K : LRV.Substructure M) (T T' : RVS M) (hT : T ≠ 0) (hT' : T' ≠ 0)
    (hind : CodeIndependent K T) (htype : CodeTypeEq K T T') :
    SameUnaryType (K : Set M) T.val T'.val := by
  intro D hD
  let D' : Set (Fin 1 → M) := {z | z 0 ∈ D ∧ iRV (z 0)}
  have hRV : (K : Set M).Definable LRV {z : Fin 1 → M | iRV (z 0)} := by
    refine Set.definable_iff_exists_formula_sum.mpr
      ⟨(Relations.formula₁ (Rel.memRV : LRV.Relations 1) (Term.var (Sum.inr (0 : Fin 1))) :
        LRV.Formula ((K : Set M) ⊕ Fin 1)),?_⟩
    ext z
    change iRV (z 0) ↔ Structure.RelMap (L := LRV) Rel.memRV _
    rw [relMap_one (M := M) Rel.memRV]
    rfl
  have hD'raw : (K : Set M).Definable LRV D' := hD.inter hRV
  have hD'sorted := raw_definableOver_sorted hc (K : Set M) (fun _ : Fin 1 => SortTag.rv) D' hD'raw
    (fun x hx i => by fin_cases i; exact hx.2)
  obtain ⟨p,ψ,hq,hw,heq⟩ := DefinableOver.quantifier_free hM hD'sorted
  let C := codeSubstructure hc K T hT hind
  let C' := codeSubstructure hc K T' hT' (htype.independent hT hT' hind)
  let Φ := codeShiftEquiv hc K T T' hT hT' hind htype
  let v : Fin p.length → C := fun i => ⟨p.values i,le_codeSubstructure hc K T hT hind (p.mem_base i)⟩
  let xs : Fin 1 → C := fun _ => ⟨T.val,code_mem_codeSubstructure hc K T hT hind⟩
  have hv : (C'.subtype ∘ Φ ∘ v) = p.values := by
    funext i
    exact codeShift_of_mem T' hT hind (p.mem_base i)
  have hxs : (C'.subtype ∘ Φ ∘ xs) = ![T'.val] := by
    funext i
    fin_cases i
    exact codeShift_code T' hT hind
  have hv0 : (C.subtype ∘ v) = p.values := rfl
  have hxs0 : (C.subtype ∘ xs) = ![T.val] := by
    funext i
    fin_cases i
    rfl
  have key : ψ.Realize p.values ![T.val] ↔ ψ.Realize p.values ![T'.val] := by
    calc ψ.Realize p.values ![T.val] ↔ ψ.Realize (C.subtype ∘ v) (C.subtype ∘ xs) := by rw [hv0,hxs0]
      _ ↔ ψ.Realize v xs := BoundedFormula.IsQF.realize_embedding hq C.subtype
      _ ↔ ψ.Realize (Φ ∘ v) (Φ ∘ xs) := (StrongHomClass.realize_boundedFormula Φ ψ).symm
      _ ↔ ψ.Realize (C'.subtype ∘ (Φ ∘ v)) (C'.subtype ∘ (Φ ∘ xs)) :=
          (BoundedFormula.IsQF.realize_embedding hq C'.subtype).symm
      _ ↔ ψ.Realize p.values ![T'.val] := by
          rw [show C'.subtype ∘ (Φ ∘ v) = p.values from hv,show C'.subtype ∘ (Φ ∘ xs) = ![T'.val] from hxs]
  have hmem (S : RVS M) : S.val ∈ D ↔ ψ.Realize p.values ![S.val] := by
    have h := Set.ext_iff.mp heq ![S.val]
    constructor
    · intro hS
      exact (h.mp ⟨hS,S.property⟩).2
    · intro hS
      exact (h.mpr ⟨fun i => by fin_cases i; exact S.property,hS⟩).1
  rw [hmem T,hmem T']
  exact key

/-! ### The automorphism -/

theorem gamma_zpow_injective_rv {T T' : RVS M} (hT : T ≠ 0) (hT' : T' ≠ 0) {m : ℤ} (hm : m ≠ 0)
    (h : Values.vrv (T ^ m) = Values.vrv (T' ^ m)) : Values.vrv T = Values.vrv T' := by
  have h0 : T.val ≠ iRVZero := fun he => hT (Subtype.ext (he.trans RVOperations.zero_val.symm))
  have h0' : T'.val ≠ iRVZero := fun he => hT' (Subtype.ext (he.trans RVOperations.zero_val.symm))
  let γ : Values.Gamma (M := M) := Values.gammaOf T h0
  let γ' : Values.Gamma (M := M) := Values.gammaOf T' h0'
  have hg : γ ^ m = γ' ^ m := by
    apply Subtype.ext
    change (Values.gammaValHom (γ ^ m)) = Values.gammaValHom (γ' ^ m)
    rw [map_zpow,map_zpow]
    change Values.vrv T ^ m = Values.vrv T' ^ m
    rw [← vrv_zpow,← vrv_zpow,h]
  have hγ : γ = γ' := zpow_left_injective hm hg
  exact congrArg (fun g : Values.Gamma (M := M) => g.val) hγ

/-- An automorphism `σ` of the monster model acting on RV codes. -/
def autRV (σ : M ≃[LRV] M) (t : RVS M) : RVS M :=
  ⟨σ t.val,by
    have h := (σ.map_rel' (Rel.memRV : LRV.Relations 1) ![t.val]).mpr
    have hh : Structure.RelMap (L := LRV) (Rel.memRV : LRV.Relations 1) ![t.val] := t.property
    have h' := h hh
    change Structure.RelMap (L := LRV) Rel.memRV (σ.toFun ∘ ![t.val]) at h'
    change Structure.RelMap (L := LRV) Rel.memRV ![σ t.val]
    convert h' using 1
    funext i
    fin_cases i
    rfl⟩

/-- One code: an automorphism over `K` carries the value of `T` to the value
of `T'`. -/
theorem exists_automorphism_code (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hh : StronglyHomogeneous M κ)
    (K : LRV.Substructure M) (hK : Cardinal.mk (K : Set M) < κ)
    (T T' : RVS M) (hT : T ≠ 0) (hT' : T' ≠ 0) (htype : CodeTypeEq K T T') :
    ∃ σ : M ≃[LRV] M, (∀ x ∈ K, σ x = x) ∧ Values.vrv (autRV σ T) = Values.vrv T' := by
  by_cases hind : CodeIndependent K T
  · have hsame := code_sameUnaryType hc K T T' hT hT' hind htype
    have hsize : Cardinal.mk ((K : Set M) ⊕ Unit) < κ := by
      simpa only [Cardinal.mk_sum,Cardinal.mk_unit,Cardinal.lift_id] using
        Cardinal.add_lt_of_lt hκ hK (Cardinal.one_lt_aleph0.trans_le hκ)
    obtain ⟨e,he⟩ := hh ((K : Set M) ⊕ Unit) (singletonAssignment (K : Set M) T.val)
      (singletonAssignment (K : Set M) T'.val) hsize hsame.partialElementary
    refine ⟨e,fun x hx => he (.inl ⟨x,hx⟩),?_⟩
    have hT'e : autRV e T = T' := Subtype.ext (he (.inr Unit.unit))
    rw [hT'e]
  · refine ⟨FirstOrder.Language.Equiv.refl LRV M,fun _ _ => rfl,?_⟩
    simp only [CodeIndependent,not_forall,not_not] at hind
    obtain ⟨m,hm,c,hc,he⟩ := hind
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0,(vrv_eq_zero_iff (0 : RVS M)).mpr rfl] at he
      exact vrv_ne_zero (zpow_ne_zero m hT) he
    have he' := (htype.eq_iff hT hT' m c hc hc0).mp he
    have hrefl : autRV (FirstOrder.Language.Equiv.refl LRV M) T = T := rfl
    rw [hrefl]
    exact gamma_zpow_injective_rv hT hT' hm (he.trans he'.symm)

end DiamondIntegral.Section2.GammaStable
