import «section 7».Lemma714Xt

/-! Lemma 7.14, part 40: slices of the first stage as unary contraction data.

For prepared contraction data `D` on `A ⊆ VF^{m+2}` and a point `b` of the base
coordinates, the slice of `g : A → Xt` at `b` (`FibreRestriction.sliceMap`) is
unary contraction data over `S⟨b⟩` for the slice `A_b` of `A`
(`PrepContr.sliceContr`), once `b` is a good point for the preimage `badA` of
the exceptional set of the first stage. Its target is the slice of `Xt`, whose
label set at `b` is the fibre of the pulled-back first-stage set (`mem_Xt_iff`),
and its form reads the form of that set at `(b, labels)` (`formX`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Reduce
open DiamondIntegral.Section6 DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.Lemma714Frozen
open DiamondIntegral.Section7.Lemma714Head DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.SpecialChains
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FiberwiseInput
open DiamondIntegral.Section7.FibreRestriction DiamondIntegral.Section7.KernelBaseChange

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem hSb' {T : LRV.Substructure M} {n : ℕ} (b : Fin n → VF M) :
    (T : Set M) ∪ Set.range (vfValues b) ⊆ (adjoin T b : Set M) := by
  rintro x (hx | ⟨i, rfl⟩)
  · exact subset_adjoin b hx
  · exact coordinate_mem_adjoin b i

section Slice
variable {T : LRV.Substructure M} {m r : ℕ} {A : DefSet (rawMixedSpace (M := M) (m + 1 + 1) r) (T : Set M)}
  {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} (D : PrepContr (G := G) A ω)

namespace PrepContr

/-! ### The form on `Xt` -/

/-- `Xt → Ã`, `(x, w) ↦ (init x, w)`. -/
def contrX : Map D.Xt D.pullSet' := D.psi.toImage.comp (D.g.inverse D.g_bijective)

theorem contrX_g (p : A) : D.contrX (D.g p) = D.psi.toImage p := by
  change D.psi.toImage (D.g.inverse D.g_bijective (D.g p)) = _
  rw [Map.inverse_apply]

theorem contrX_val (x : D.Xt) : (D.contrX x).val = (Fin.init x.val.1, x.val.2) := by
  obtain ⟨p, rfl⟩ := D.g_bijective.2 x
  rw [contrX_g]
  change (D.psi p).val = (Fin.init (D.g p).val.1, (D.g p).val.2)
  rw [psi_val, D.g_fix]
  rfl

/-- The form on `Xt`: the form of the pulled-back first-stage set at `(init, labels)`. -/
def formX : Map D.Xt (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)) := D.ω₁.comp D.contrX

theorem formX_g (p : A) : (D.formX (D.g p)).val = (ω p).val := by
  change (D.ω₁ (D.contrX (D.g p))).val = _
  rw [contrX_g]
  change ((restForm D.C.data) (D.prep₁ (D.psi.toImage p))).val = _
  rw [prep₁_apply]
  exact (restForm_contraction D.C.data (D.prep p)).trans (D.transport p)

theorem formX_eq (x y : D.Xt) (h1 : Fin.init x.val.1 = Fin.init y.val.1) (h2 : x.val.2 = y.val.2) :
    D.formX x = D.formX y := by
  change D.ω₁ (D.contrX x) = D.ω₁ (D.contrX y)
  congr 1
  apply Subtype.ext
  rw [contrX_val, contrX_val, h1, h2]

/-! ### Membership in `Xt` -/

theorem g_mem (p : A) : (D.g p).val ∈ D.Xt.carrier := (D.g p).property

/-- Moving the last coordinate within its RV class stays in `Xt`. -/
theorem Xt_rv_move (p₀ : A) (b : Fin (m + 1) → VF M) (hb : Fin.init p₀.val.1 = b) (x : VF M)
    (hx : rv M x = rv M ((D.st.lift (D.prep p₀)).val.1 (Fin.last (m + 1)))) :
    ((Fin.snoc (α := fun _ => VF M) b x, (D.st.lift (D.prep p₀)).val.2) : Mixed M (m + 1 + 1) D.st.arity) ∈
      D.Xt.carrier := by
  have hz₀ := (D.st.recover_target (D.st.lift (D.prep p₀)).val).mp (D.st.lift (D.prep p₀)).property
  let z' : Mixed M (m + 1 + 1) D.st.arity :=
    (Fin.snoc (α := fun _ => VF M) (Fin.init (D.st.lift (D.prep p₀)).val.1) x, (D.st.lift (D.prep p₀)).val.2)
  have hz' : z' ∈ D.st.target.carrier := by
    refine (D.st.recover_target z').mpr ⟨?_, ?_⟩
    · change ((Fin.init (Fin.snoc (α := fun _ => VF M) (Fin.init (D.st.lift (D.prep p₀)).val.1) x)),
        (D.st.lift (D.prep p₀)).val.2) ∈ D.st.contracted.carrier
      rw [Fin.init_snoc]
      exact hz₀.1
    · change rv M (Fin.snoc (α := fun _ => VF M) (Fin.init (D.st.lift (D.prep p₀)).val.1) x (Fin.last (m + 1))) = _
      rw [Fin.snoc_last, hx]
      exact hz₀.2
  obtain ⟨p₁, hp₁⟩ := D.liftPrep_bijective.2 ⟨z', hz'⟩
  have hp₁v : (D.st.lift (D.prep p₁)).val = z' := congrArg Subtype.val hp₁
  have hl : (D.st.lift (D.prep p₁)).val.2 = (D.st.lift (D.prep p₀)).val.2 := by rw [hp₁v]
  have hi : Fin.init p₁.val.1 = b := by
    have h1 := D.lift_init p₁
    have h0 := D.lift_init p₀
    rw [hp₁v] at h1
    change Fin.init (Fin.snoc (α := fun _ => VF M) (Fin.init (D.st.lift (D.prep p₀)).val.1) x) = _ at h1
    rw [Fin.init_snoc, h0, trAt_eq_of_lift D hl, hb] at h1
    exact (add_right_cancel h1).symm
  refine ⟨p₁, ?_⟩
  change (D.g p₁).val = _
  rw [g_val, hi, hl, hp₁v]
  change ((Fin.snoc (α := fun _ => VF M) b
    (Fin.snoc (α := fun _ => VF M) (Fin.init (D.st.lift (D.prep p₀)).val.1) x (Fin.last (m + 1))), _) :
      Mixed M (m + 1 + 1) D.st.arity) = _
  rw [Fin.snoc_last]

/-! ### The exceptional set in the coordinates of `A` -/

/-- The preimage of the exceptional set of the first stage. -/
def badA : DefSet (rawMixedSpace (M := M) (m + 1 + 1) r) (T : Set M) :=
  ⟨{x | ∃ p : A, p.val = x ∧ (D.prep p).val ∈ D.st.exceptional.carrier},
    D.prep.definable_preimage D.st.exceptional.definable⟩

theorem badA_subset : D.badA.carrier ⊆ A.carrier := by
  rintro _ ⟨p, rfl, -⟩
  exact p.property

theorem notMem_badA (p : A) (h : p.val ∉ D.badA.carrier) : (D.prep p).val ∉ D.st.exceptional.carrier :=
  fun he => h ⟨p, rfl, he⟩

theorem badA_dim : vfDim (rawRVSpace (M := M) 1) D.badA < m + 1 + 1 := by
  let f₀ : Map D.badA D.Y := D.prep.restrict D.badA_subset
  have hmem : ∀ a : D.badA, (f₀ a).val ∈ D.st.exceptional.carrier := by
    rintro ⟨x, p, rfl, he⟩
    exact he
  let f : Map D.badA D.st.exceptional := f₀.corestrict hmem
  have hinj : Function.Injective f := by
    intro a a' he
    have h1 : (f a).val = (f a').val := congrArg Subtype.val he
    change (f₀ a).val = (f₀ a').val at h1
    have h2 := D.homeo.bijective.1 (Subtype.ext h1 : D.prep ⟨a.val, D.badA_subset a.property⟩ =
      D.prep ⟨a'.val, D.badA_subset a'.property⟩)
    have h3 : a.val = a'.val := congrArg (fun z : A => z.val) h2
    exact Subtype.ext h3
  exact lt_of_le_of_lt (vfDim_le_of_finite_map (rawRVSpace (M := M) 1) f (Map.finiteFibres_of_injective hinj))
    D.st.exceptional_dim

/-! ### The slice contraction data -/

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

theorem slice_lift (b : Fin (m + 1) → VF M) (q : sliceSet D.Xt b (hSb' b)) :
    ∃ p₀ : A, Fin.init p₀.val.1 = b ∧ q.val.1 0 = (D.st.lift (D.prep p₀)).val.1 (Fin.last (m + 1)) ∧
      q.val.2 = (D.st.lift (D.prep p₀)).val.2 := by
  obtain ⟨p₀, hp₀⟩ := q.property
  have hv : (D.g p₀).val = ((Fin.snoc b (q.val.1 0), q.val.2) : Mixed M (m + 1 + 1) D.st.arity) := hp₀
  rw [g_val] at hv
  obtain ⟨h1, h2⟩ := Prod.mk.inj hv
  refine ⟨p₀, ?_, ?_, h2.symm⟩
  · have := congrArg Fin.init h1
    simpa only [Fin.init_snoc] using this
  · have := congrFun h1 (Fin.last (m + 1))
    simp only [Fin.snoc_last] at this
    exact this.symm

include h00 hc hκ hs hv hsmall hΓ in
/-- **The slice of the first stage at a good point is unary contraction data
over `S⟨b⟩`.** -/
def sliceContr (hA : ProperInvariant (T : Set M) A.carrier) (b : Fin (m + 1) → VF M)
    (hgood : vfDim (rawRVSpace (M := M) 1) (sliceSet D.badA b (hSb' b)) < 1 ∨
      (sliceSet D.badA b (hSb' b)).carrier = ∅) :
    UnaryContr (G := G) (T := adjoin T b) (sliceSet A b (hSb' b)) (sliceForm A ω b (hSb' b)) where
  s := D.st.arity
  target := sliceSet D.Xt b (hSb' b)
  map := sliceMap D.g D.g_fix
  homeo := sliceMap_homeomorphism D.g_fix (D.g_homeo h00 hc hκ hs hv hsmall hΓ hA.vfBounded)
  oldIndex := D.st.oldLabels ∘ D.oldIndex
  retained := fun q j => by
    change (sliceMap D.g D.g_fix q).val.2 (D.st.oldLabels (D.oldIndex j)) = q.val.2 j
    rw [sliceMap_val]
    change (D.g (liftElem q)).val.2 (D.st.oldLabels (D.oldIndex j)) = q.val.2 j
    rw [g_val]
    change (D.st.lift (D.prep (liftElem q))).val.2 (D.st.oldLabels (D.oldIndex j)) = q.val.2 j
    rw [D.st.retained, D.retained]
    rfl
  form := sliceForm D.Xt D.formX b (hSb' b)
  form_transport := fun q => by
    change gammaMapValue (sliceForm D.Xt D.formX b (hSb' b)) (sliceMap D.g D.g_fix q) =
      gammaMapValue (sliceForm A ω b (hSb' b)) q
    rw [sliceForm_apply, sliceForm_apply]
    change gammaMapValue D.formX (liftElem (sliceMap D.g D.g_fix q)) = gammaMapValue ω (liftElem q)
    rw [liftElem_sliceMap D.g_fix q]
    exact D.formX_g (liftElem q)
  form_same_tags := fun x y h => by
    apply Subtype.ext
    change gammaMapValue (sliceForm D.Xt D.formX b (hSb' b)) x = gammaMapValue (sliceForm D.Xt D.formX b (hSb' b)) y
    rw [sliceForm_apply, sliceForm_apply]
    have e : D.formX ⟨(Fin.snoc b (x.val.1 0), x.val.2), x.property⟩ =
        D.formX ⟨(Fin.snoc b (y.val.1 0), y.val.2), y.property⟩ :=
      D.formX_eq _ _ (by simp only [Fin.init_snoc]) h
    exact congrArg Subtype.val e
  pullback := by
    apply Set.Subset.antisymm _ (subset_rvHull _)
    intro q hq
    obtain ⟨p, hp, hVF, hRV⟩ := (mem_rvHull_iff _ q).mp hq
    obtain ⟨p₀, hb, hx, hl⟩ := D.slice_lift b ⟨p, hp⟩
    change ((Fin.snoc b (q.1 0), q.2) : Mixed M (m + 1 + 1) D.st.arity) ∈ D.Xt.carrier
    have hrv : rv M (q.1 0) = rv M ((D.st.lift (D.prep p₀)).val.1 (Fin.last (m + 1))) := by
      have := congrFun hVF 0
      change rv M (p.1 0) = rv M (q.1 0) at this
      rw [← this]
      exact congrArg (rv M) hx
    have hq2 : q.2 = (D.st.lift (D.prep p₀)).val.2 := hRV.symm.trans hl
    rw [hq2]
    exact D.Xt_rv_move p₀ b hb (q.1 0) hrv
  vfBounded := by
    obtain ⟨γ, hγ⟩ := D.st.doublyBounded
    refine ⟨γ, fun q hq i => ?_⟩
    obtain ⟨p₀, -, hx, -⟩ := D.slice_lift b ⟨q, hq⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change (γ⁻¹).val ≤ vfValue (q.1 0) ∧ vfValue (q.1 0) ≤ γ.val
    rw [hx]
    exact hγ _ (D.st.lift (D.prep p₀)).property (Fin.last (m + 1))
  proper := sliceSet_properInvariant (D.Xt_proper hA.vfBounded)
  tagged := by
    intro q hq q' hq' h
    obtain ⟨p₀, -, hx, hl⟩ := D.slice_lift b ⟨q, hq⟩
    obtain ⟨p₁, -, hx', hl'⟩ := D.slice_lift b ⟨q', hq'⟩
    have r0 := ((D.st.recover_target (D.st.lift (D.prep p₀)).val).mp (D.st.lift (D.prep p₀)).property).2
    have r1 := ((D.st.recover_target (D.st.lift (D.prep p₁)).val).mp (D.st.lift (D.prep p₁)).property).2
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change rv M (q.1 0) = rv M (q'.1 0)
    change q.2 = q'.2 at h
    rw [hx, hx', r0, r1, ← hl, ← hl', h]
  unit := fun q hInd => by
    have hq : q.val ∉ (sliceSet D.badA b (hSb' b)).carrier := by
      rcases hgood with hd | he
      · exact not_mem_small_set_of_independent hc _ hd q.val hInd
      · rw [he]
        exact Set.notMem_empty _
    have hp : (D.prep (liftElem q)).val ∉ D.st.exceptional.carrier := D.notMem_badA (liftElem q) hq
    obtain ⟨L, hL, hdet⟩ := D.g_unit hv hA.vfBounded (liftElem q) hp
    obtain ⟨L₁, hL₁, hdet₁⟩ := sliceMap_derivative D.g D.g_fix q hL
    exact ⟨L₁, hL₁, hdet₁.trans hdet⟩

end PrepContr

end Slice

end DiamondIntegral.Section7.Lemma714Reduce
