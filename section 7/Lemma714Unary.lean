import «section 7».Lemma714FrozenExists
import «section 7».Lemma714Bounds
import «section 7».Lemma714Descent
import «section 7».Lemma714Cover

/-! Lemma 7.14, part 32: the unary case.

`unary_of_descent` assembles the unary argument around a descent step: the VF
projection `P` of `A'` is frozen against the fibre families and the given
witness sets (`exists_frozen`); the standard contractions are compared with the
frozen sets (`muIsp_compare`); the frozen sets have the head-start classes of
the descended indexed objects (`cls_ind_eq_clsH`). The descent step itself is
the gluing of witness schemata valid at all keys (`muIsp_ind_cover` in positive
fibre degree, `cls_ind0_cover` in degree `0`).

**The unary case of Lemma 7.14** (`unary_muIsp`): for unary `A'`, `A''` with the
same VF projection, fibrewise `μIsp^db` of the head-start fibres gives `μIsp` of
the head-start classes of any two unary standard contractions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Frozen
open DiamondIntegral.Section6
open DiamondIntegral.Section7.Lemma714Prod DiamondIntegral.Section7.Lemma714Schema DiamondIntegral.Section7.Lemma714Head
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.FibreObjects DiamondIntegral.Section7.FiberwiseInput
open DiamondIntegral.Section7.ElementaryComparison DiamondIntegral.Section7.ElementaryBlowups

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

section Unary
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  {T : LRV.Substructure M} (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M))
  (hTV : (T : Set M) ⊆ algebraicClosureSet V) (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
  (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
  {r' r'' k : ℕ} {A' : DefSet (rawMixedSpace (M := M) 1 r') (T : Set M)}
  {A'' : DefSet (rawMixedSpace (M := M) 1 r'') (T : Set M)}
  (ω' : Map A' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
  (ω'' : Map A'' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
  (hA' : ProperInvariant (T : Set M) A'.carrier) (hA'' : ProperInvariant (T : Set M) A''.carrier)
  (hVF : ∀ a : Fin 1 → VF M, (∃ u, (a, u) ∈ A'.carrier) ↔ (∃ v, (a, v) ∈ A''.carrier))
  (π' : Fin k → Fin r') (π'' : Fin k → Fin r'')
  (hFin' : ∀ (a : Fin 1 → VF M) (t : Fin k → RVInfinity M),
    {u : Fin r' → RVInfinity M | (a, u) ∈ A'.carrier ∧ u ∘ π' = t}.Finite)
  (hFin'' : ∀ (a : Fin 1 → VF M) (t : Fin k → RVInfinity M),
    {u : Fin r'' → RVInfinity M | (a, u) ∈ A''.carrier ∧ u ∘ π'' = t}.Finite)
  (N' N'' : ℕ)

theorem hAP_left : ∀ p ∈ A'.carrier, basePoint p ∈ (vfBase A').carrier := fun _ hp => mem_vfBase A' hp

include hVF in
theorem hAP_right : ∀ p ∈ A''.carrier, basePoint p ∈ (vfBase A').carrier := by
  intro p hp
  change (p.1, (Fin.elim0 : Fin 0 → RVInfinity M)) ∈ (vfBase A').carrier
  rw [vfBase_mem_iff]
  exact (hVF p.1).mpr ⟨p.2, hp⟩

include hc h00 hκ hs hv hV hVT hTV hnt hsmall hΓ hA' hA'' hVF in
/-- **The unary case around a descent step.** -/
theorem unary_of_descent
    (hX0 : ∀ b ∈ (vfBase A').carrier, (famSchema hc A' ω' π' N').Valid (vfValues b.1))
    (hY0 : ∀ b ∈ (vfBase A').carrier, (famSchema hc A'' ω'' π'' N'').Valid (vfValues b.1))
    (L₀ : List (Comp (⟨(T : Set M), ∅⟩ : Base (M := M)) (vfs 1)))
    (hdesc : ∀ Z : Frozen (G := G) (vfBase A'),
      (∀ x, AllRowConst (Z.K hc) ((famSchema hc A' ω' π' N').comps ++ (famSchema hc A'' ω'' π'' N'').comps ++ L₀) x) →
      ∀ (hQ : (Z.Q hc).AllBounds)
        (hW' : ∀ x ∈ (Z.Q hc).carrier, ((famSchema hc A' ω' π' N').recode (Z.K hc)).Valid x)
        (hW'' : ∀ x ∈ (Z.Q hc).carrier, ((famSchema hc A'' ω'' π'' N'').recode (Z.K hc)).Valid x),
        MuIsp (cls ((Z.Q hc).indObj hQ.bounds _ hW')) (cls ((Z.Q hc).indObj hQ.bounds _ hW'')))
    {e : Equiv.Perm (Fin (0 + 1))}
    (F' : NormalizedMeasuredContraction (G := G) A' ω' e) (F'' : NormalizedMeasuredContraction (G := G) A'' ω'' e) :
    MuIsp (clsH hc (targetHGood hc h00 hκ hs hv hsmall hΓ F' π' hFin'))
      (clsH hc (targetHGood hc h00 hκ hs hv hsmall hΓ F'' π'' hFin'')) := by
  let X₀ := famSchema hc A' ω' π' N'
  let Y₀ := famSchema hc A'' ω'' π'' N''
  have hP := vfBase_properInvariant h00 hc lin hκ hs hv hsmall hΓ A' hA'
  have hAP' := hAP_left (A' := A')
  have hAP'' := hAP_right hVF
  have hF' := F'.homeomorphism h00 hc lin hκ hs hv hsmall hΓ
  have hF'' := F''.homeomorphism h00 hc lin hκ hs hv hsmall hΓ
  have hω' := levels_open_of_transport hv F'.map hF'.covariant F'.form F'.form_same_tags ω'
    (fun p => Subtype.ext (F'.form_transport p).symm)
  have hω'' := levels_open_of_transport hv F''.map hF''.covariant F''.form F''.form_same_tags ω''
    (fun p => Subtype.ext (F''.form_transport p).symm)
  obtain ⟨Z, hG', hG'', hRC⟩ := exists_frozen (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ hP ω' ω'' hAP' hAP''
    hA' hA'' hω' hω'' (X₀.comps ++ Y₀.comps ++ L₀)
  have hRC' : FamRowConst Z hc ω' π' N' := fun x => X₀.rowConst_of fun c hcm => hRC x c (by simp [hcm])
  have hRC'' : FamRowConst Z hc ω'' π'' N'' := fun x => Y₀.rowConst_of fun c hcm => hRC x c (by simp [hcm])
  have hQ : (Z.Q hc).AllBounds := allBounds hc h00 hκ hs hsmall hΓ (Z.Q hc)
    (keySet_nonzero_all Z.Bk hc Z.rvBounded Z.pullback Z.finite)
    (keySet_codeBounded Z.Bk hc Z.rvBounded Z.pullback Z.finite)
  have hxs : ∀ q : regT Z.Bk, ∀ i, sortEval (rvs (1 + Z.sk) i) (rvValues q.val.2 i) := fun q i => (q.val.2 i).property
  have hzs : ∀ b : vfBase A', ∀ i, sortEval (vfs 1 i) (vfValues b.val.1 i) := fun b i => (b.val.1 i).property
  have hW' : ∀ x ∈ (Z.Q hc).carrier, (X₀.recode (Z.K hc)).Valid x := by
    rintro _ ⟨qv, hqv, rfl⟩
    let q : regT Z.Bk := ⟨qv, hqv⟩
    exact ChartSchema.recode_valid (hxs q) (hzs _) (Z.K_mk_ρ hc q) (hRC' _) (hX0 _ (Subtype.property _))
  have hW'' : ∀ x ∈ (Z.Q hc).carrier, (Y₀.recode (Z.K hc)).Valid x := by
    rintro _ ⟨qv, hqv, rfl⟩
    let q : regT Z.Bk := ⟨qv, hqv⟩
    exact ChartSchema.recode_valid (hxs q) (hzs _) (Z.K_mk_ρ hc q) (hRC'' _) (hY0 _ (Subtype.property _))
  have hd := hdesc Z hRC hQ hW' hW''
  rw [cls_ind_eq_clsH Z hc ω' π' N' hAP' h00 hκ hs hv hsmall hA' hFin' hX0 hG' hRC' hQ hW',
    cls_ind_eq_clsH Z hc ω'' π'' N'' hAP'' h00 hκ hs hv hsmall hA'' hFin'' hY0 hG'' hRC'' hQ hW''] at hd
  have hc' := muIsp_compare Z hc ω' π' N' hAP' h00 hκ hs hv hsmall hA' hFin' hΓ V hV hVT hTV hnt hG' hRC' F'
  have hc'' := muIsp_compare Z hc ω'' π'' N'' hAP'' h00 hκ hs hv hsmall hA'' hFin'' hΓ V hV hVT hTV hnt hG'' hRC'' F''
  have hE : ElementaryDiamond (BT T) k := elementaryDiamond
  exact muIsp_trans hE (muIsp_trans hE hc' hd) (muIsp_symm hc'')

end Unary

/-! ### The descent steps -/

section Descent
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  {T : LRV.Substructure M} (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M))
  (hTV : (T : Set M) ⊆ algebraicClosureSet V) (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
  (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
  {r' r'' : ℕ} {A' : DefSet (rawMixedSpace (M := M) 1 r') (T : Set M)}
  {A'' : DefSet (rawMixedSpace (M := M) 1 r'') (T : Set M)}
  (ω' : Map A' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
  (ω'' : Map A'' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
  (hA' : ProperInvariant (T : Set M) A'.carrier) (hA'' : ProperInvariant (T : Set M) A''.carrier)
  (hVF : ∀ a : Fin 1 → VF M, (∃ u, (a, u) ∈ A'.carrier) ↔ (∃ v, (a, v) ∈ A''.carrier))

include hc h00 hκ hs hv hV hVT hTV hnt hsmall hΓ hA' hA'' hVF in
/-- **The unary case of Lemma 7.14, positive fibre degree.** -/
theorem unary_pos {k₀ : ℕ} (π' : Fin (1 + k₀) → Fin r') (π'' : Fin (1 + k₀) → Fin r'')
    (hFin' : ∀ (a : Fin 1 → VF M) (t : Fin (1 + k₀) → RVInfinity M),
      {u : Fin r' → RVInfinity M | (a, u) ∈ A'.carrier ∧ u ∘ π' = t}.Finite)
    (hFin'' : ∀ (a : Fin 1 → VF M) (t : Fin (1 + k₀) → RVInfinity M),
      {u : Fin r'' → RVInfinity M | (a, u) ∈ A''.carrier ∧ u ∘ π'' = t}.Finite)
    (hNZ' : ∀ p ∈ A'.carrier, ∀ i, (p.2 (π' i)).val ≠ iRVZero)
    (hNZ'' : ∀ p ∈ A''.carrier, ∀ i, (p.2 (π'' i)).val ≠ iRVZero)
    (hFibre : ∀ a : Fin 1 → VF M, (∃ u, (a, u) ∈ A'.carrier) →
      ∃ (hU' : (fibreObject T A' ω' a π' (hFin' a) hNZ').doublyBounded)
        (hU'' : (fibreObject T A'' ω'' a π'' (hFin'' a) hNZ'').doublyBounded),
        IspRel (cls (objOf hc (KernelBaseChange.adjoin T a) _ hU')) (cls (objOf hc (KernelBaseChange.adjoin T a) _ hU'')))
    {e : Equiv.Perm (Fin (0 + 1))}
    (F' : NormalizedMeasuredContraction (G := G) A' ω' e) (F'' : NormalizedMeasuredContraction (G := G) A'' ω'' e) :
    MuIsp (clsH hc (targetHGood hc h00 hκ hs hv hsmall hΓ F' π' hFin'))
      (clsH hc (targetHGood hc h00 hκ hs hv hsmall hΓ F'' π'' hFin'')) := by
  obtain ⟨N', hN'⟩ := exists_fam_bound hc A' ω' π' hκ.le hs hsmall hFin'
  obtain ⟨N'', hN''⟩ := exists_fam_bound hc A'' ω'' π'' hκ.le hs hsmall hFin''
  have hXv : ∀ a : Fin 1 → VF M, (∃ u, (a, u) ∈ A'.carrier) → (famSchema hc A' ω' π' N').Valid (vfValues a) := by
    intro a ha
    obtain ⟨hU', -, -⟩ := hFibre a ha
    exact famSchema_valid hc A' ω' π' N' a (hFin' a) hNZ' (fun y hy => hN' a y hy) hU'
  have hYv : ∀ a : Fin 1 → VF M, (∃ u, (a, u) ∈ A'.carrier) → (famSchema hc A'' ω'' π'' N'').Valid (vfValues a) := by
    intro a ha
    obtain ⟨-, hU'', -⟩ := hFibre a ha
    exact famSchema_valid hc A'' ω'' π'' N'' a (hFin'' a) hNZ'' (fun y hy => hN'' a y hy) hU''
  obtain ⟨J, hJ⟩ := exists_witness_cover hc hκ hs hsmall A' hXv hYv (by
    intro a ha
    obtain ⟨hU', hU'', hI⟩ := hFibre a ha
    rwa [cls_fibre_eq hc A' ω' π' N' a (hFin' a) hNZ' (hXv a ha) hU',
      cls_fibre_eq hc A'' ω'' π'' N'' a (hFin'' a) hNZ'' (hYv a ha) hU''] at hI)
  have hX0 : ∀ b ∈ (vfBase A').carrier, (famSchema hc A' ω' π' N').Valid (vfValues b.1) :=
    fun b hb => hXv b.1 ((vfBase_mem_iff A' b.1 b.2).mp hb)
  have hY0 : ∀ b ∈ (vfBase A').carrier, (famSchema hc A'' ω'' π'' N'').Valid (vfValues b.1) :=
    fun b hb => hYv b.1 ((vfBase_mem_iff A' b.1 b.2).mp hb)
  refine unary_of_descent hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ ω' ω'' hA' hA'' hVF π' π'' hFin' hFin'' N' N''
    hX0 hY0 (J.toList.flatMap WitnessSchema.comps) ?_ F' F''
  intro Z hRC hQ hW' hW''
  refine KeySet.muIsp_ind_cover (J.toList.map (fun W => W.recode (Z.K hc))) (Z.Q hc) hQ hW' hW'' ?_
  rintro _ ⟨qv, hqv, rfl⟩
  let q : regT Z.Bk := ⟨qv, hqv⟩
  let b := Z.Φ₀.inverse Z.bij₀ (frz Z.F (Z.ρ q))
  obtain ⟨W, hWJ, hWv⟩ := hJ b.val.1 ((vfBase_mem_iff A' b.val.1 b.val.2).mp b.property)
  refine ⟨W.recode (Z.K hc), List.mem_map.mpr ⟨W, Finset.mem_toList.mpr hWJ, rfl⟩, ?_⟩
  exact WitnessSchema.recode_valid (fun i => (q.val.2 i).property) (fun i => (b.val.1 i).property) (Z.K_mk_ρ hc q)
    (W.rowConst_of fun c hcm => hRC _ c
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨W, Finset.mem_toList.mpr hWJ, hcm⟩))) hWv

include hc h00 hκ hs hv hV hVT hTV hnt hsmall hΓ hA' hA'' hVF in
/-- **The unary case of Lemma 7.14, fibre degree `0`.** -/
theorem unary_zero (π' : Fin 0 → Fin r') (π'' : Fin 0 → Fin r'')
    (hFin' : ∀ (a : Fin 1 → VF M) (t : Fin 0 → RVInfinity M),
      {u : Fin r' → RVInfinity M | (a, u) ∈ A'.carrier ∧ u ∘ π' = t}.Finite)
    (hFin'' : ∀ (a : Fin 1 → VF M) (t : Fin 0 → RVInfinity M),
      {u : Fin r'' → RVInfinity M | (a, u) ∈ A''.carrier ∧ u ∘ π'' = t}.Finite)
    (hNZ' : ∀ p ∈ A'.carrier, ∀ i, (p.2 (π' i)).val ≠ iRVZero)
    (hNZ'' : ∀ p ∈ A''.carrier, ∀ i, (p.2 (π'' i)).val ≠ iRVZero)
    (hFibre : ∀ a : Fin 1 → VF M, (∃ u, (a, u) ∈ A'.carrier) →
      ∃ (hU' : (fibreObject T A' ω' a π' (hFin' a) hNZ').doublyBounded)
        (hU'' : (fibreObject T A'' ω'' a π'' (hFin'' a) hNZ'').doublyBounded),
        IspRel (cls (objOf hc (KernelBaseChange.adjoin T a) _ hU')) (cls (objOf hc (KernelBaseChange.adjoin T a) _ hU'')))
    {e : Equiv.Perm (Fin (0 + 1))}
    (F' : NormalizedMeasuredContraction (G := G) A' ω' e) (F'' : NormalizedMeasuredContraction (G := G) A'' ω'' e) :
    MuIsp (clsH hc (targetHGood hc h00 hκ hs hv hsmall hΓ F' π' hFin'))
      (clsH hc (targetHGood hc h00 hκ hs hv hsmall hΓ F'' π'' hFin'')) := by
  obtain ⟨N', hN'⟩ := exists_fam_bound hc A' ω' π' hκ.le hs hsmall hFin'
  obtain ⟨N'', hN''⟩ := exists_fam_bound hc A'' ω'' π'' hκ.le hs hsmall hFin''
  have hXv : ∀ a : Fin 1 → VF M, (∃ u, (a, u) ∈ A'.carrier) → (famSchema hc A' ω' π' N').Valid (vfValues a) := by
    intro a ha
    obtain ⟨hU', -, -⟩ := hFibre a ha
    exact famSchema_valid hc A' ω' π' N' a (hFin' a) hNZ' (fun y hy => hN' a y hy) hU'
  have hYv : ∀ a : Fin 1 → VF M, (∃ u, (a, u) ∈ A'.carrier) → (famSchema hc A'' ω'' π'' N'').Valid (vfValues a) := by
    intro a ha
    obtain ⟨-, hU'', -⟩ := hFibre a ha
    exact famSchema_valid hc A'' ω'' π'' N'' a (hFin'' a) hNZ'' (fun y hy => hN'' a y hy) hU''
  obtain ⟨J, hJ⟩ := exists_witness_cover0 hc hκ hs hsmall A' hXv hYv (by
    intro a ha
    obtain ⟨hU', hU'', hI⟩ := hFibre a ha
    rw [ispRel_zero] at hI
    rwa [cls_fibre_eq hc A' ω' π' N' a (hFin' a) hNZ' (hXv a ha) hU',
      cls_fibre_eq hc A'' ω'' π'' N'' a (hFin'' a) hNZ'' (hYv a ha) hU''] at hI)
  have hX0 : ∀ b ∈ (vfBase A').carrier, (famSchema hc A' ω' π' N').Valid (vfValues b.1) :=
    fun b hb => hXv b.1 ((vfBase_mem_iff A' b.1 b.2).mp hb)
  have hY0 : ∀ b ∈ (vfBase A').carrier, (famSchema hc A'' ω'' π'' N'').Valid (vfValues b.1) :=
    fun b hb => hYv b.1 ((vfBase_mem_iff A' b.1 b.2).mp hb)
  refine unary_of_descent hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ ω' ω'' hA' hA'' hVF π' π'' hFin' hFin'' N' N''
    hX0 hY0 (J.toList.flatMap WitnessSchema0.comps) ?_ F' F''
  intro Z hRC hQ hW' hW''
  have heq := KeySet.cls_ind0_cover (J.toList.map (fun W => W.recode (Z.K hc))) (Z.Q hc) hQ hW' hW'' (by
    rintro _ ⟨qv, hqv, rfl⟩
    let q : regT Z.Bk := ⟨qv, hqv⟩
    let b := Z.Φ₀.inverse Z.bij₀ (frz Z.F (Z.ρ q))
    obtain ⟨W, hWJ, hWv⟩ := hJ b.val.1 ((vfBase_mem_iff A' b.val.1 b.val.2).mp b.property)
    refine ⟨W.recode (Z.K hc), List.mem_map.mpr ⟨W, Finset.mem_toList.mpr hWJ, rfl⟩, ?_⟩
    exact WitnessSchema0.recode_valid (fun i => (q.val.2 i).property) (fun i => (b.val.1 i).property) (Z.K_mk_ρ hc q)
      (W.rowConst_of fun c hcm => hRC _ c
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨W, Finset.mem_toList.mpr hWJ, hcm⟩))) hWv)
  rw [heq]
  exact muIsp_refl _

end Descent

end DiamondIntegral.Section7.Lemma714Frozen
