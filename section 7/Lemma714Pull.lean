import «section 7».Lemma714Prep

/-! Lemma 7.14, part 37: first-stage sets pulled back to the common projection.

For prepared contraction data `D = (prep : A → Y, C)` with `A ⊆ VF^{m+2}`, let
`st` be the first stage of `C`: it contracts the last VF coordinate of `Y`,
fixes the others and keeps the old labels. Its contracted set `Y₁` has VF
coordinates `init(prep p)`, which are shifted from `init p` by the
label-determined translation of `prep` (GAP-REPAIRS 11). The **pulled-back
first-stage set**

  `Ã = {(init p, labels of st(prep p)) | p ∈ A}`  (`pullSet'`)

has the VF projection `init(A_VF)`, which is the same for `A'` and `A''`, and
the descended map `prep₁ : Ã → Y₁` (`prep₁`) is a label translation. With the
rest of `C` on `Y₁` this gives prepared contraction data `D.rest` on `Ã`
(`PrepContr.rest`), whose head-start class with head start `k + 1` is the
head-start class of `D` with head start `k` (`cls_rest`). -/

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

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-! ### The code map `((x, u), (z, w)) ↦ (init x, w)` -/

section InitLabels
variable {S : Set M} {m r a : ℕ}

def ilPoint (x : Mixed M (m + 1) r × Mixed M (m + 1) a) : Mixed M m a := (Fin.init x.1.1, x.2.2)

def ilCodes (z : (Fin (m + 1) ⊕ Fin r) ⊕ (Fin (m + 1) ⊕ Fin a) → M) : Fin m ⊕ Fin a → M :=
  Sum.elim (fun i => z (.inl (.inl i.castSucc))) (fun j => z (.inr (.inr j)))

omit hM in
theorem mixedValues_il (x : Mixed M (m + 1) r × Mixed M (m + 1) a) :
    mixedValues (ilPoint x) = ilCodes (Sum.elim (mixedValues x.1) (mixedValues x.2)) := by
  funext i
  rcases i with i | i <;> rfl

/-- The code map `((x, u), (z, w)) ↦ (init x, w)`. -/
def initLabels (C : DefSet ((rawMixedSpace (M := M) (m + 1) r).prod (rawMixedSpace (M := M) (m + 1) a)) S) :
    Map C (DefSet.univ (rawMixedSpace (M := M) m a) S) := by
  have hc : ∀ c : ((rawMixedSpace (M := M) (m + 1) r).prod (rawMixedSpace (M := M) (m + 1) a)).domain,
      (ilCodes c.val : Fin m ⊕ Fin a → M) =
        mixedValues (ilPoint (((rawMixedSpace (M := M) (m + 1) r).prod (rawMixedSpace (M := M) (m + 1) a)).decode c)) := by
    intro c
    rw [mixedValues_il]
    apply congrArg ilCodes
    funext i
    rcases i with i | i
    · exact (congrFun (mixedValues_decode (⟨c.val ∘ Sum.inl, c.property.1⟩ : (rawMixedSpace (M := M) (m + 1) r).domain)) i).symm
    · exact (congrFun (mixedValues_decode (⟨c.val ∘ Sum.inr, c.property.2⟩ : (rawMixedSpace (M := M) (m + 1) a).domain)) i).symm
  refine Map.ofCodes C ilPoint ilCodes ?_ ?_ ?_
  · rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  · intro c
    rw [hc c]
    exact mixedValues_mem_domain _
  · intro c
    apply mixedValues_injective
    exact (mixedValues_decode _).trans (hc c)

@[simp] theorem initLabels_apply
    (C : DefSet ((rawMixedSpace (M := M) (m + 1) r).prod (rawMixedSpace (M := M) (m + 1) a)) S) (x : C) :
    (initLabels C x).val = ilPoint x.val := rfl

end InitLabels

/-! ### Translation invariance of proper invariance -/

section TranslInvariant
variable {S : Set M} {m q : ℕ}

theorem alphaInvariant_translate {α : Fin m → Gamma M} {X : Set (Fin m → VF M)} (hX : AlphaInvariant α X)
    (c : Fin m → VF M) : AlphaInvariant α {a | a + c ∈ X} := by
  intro a b hab
  have h : Congruent α (a + c) (b + c) := by
    intro i
    have := hab i
    simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using this
  exact hX (a + c) (b + c) h

/-- A set mapped onto a proper invariant set by a label-preserving translation
bijection is proper invariant, once it is VF bounded. -/
theorem properInvariant_of_transl {X Y : DefSet (rawMixedSpace (M := M) m q) S} (f : Map X Y)
    (hf : Function.Bijective f) (hlab : ∀ p : X, (f p).val.2 = p.val.2)
    (htr : ∀ p p' : X, p.val.2 = p'.val.2 → trAt f p = trAt f p')
    (hY : ProperInvariant S Y.carrier) (hXb : VFBounded X.carrier) : ProperInvariant S X.carrier := by
  refine ⟨X.definable, hXb, ?_, fun t => ?_⟩
  · obtain ⟨γ, hγ⟩ := hY.rvBounded
    refine ⟨γ, fun p hp i => ?_⟩
    have := hγ (f ⟨p, hp⟩).val (f ⟨p, hp⟩).property i
    rwa [hlab] at this
  · obtain ⟨α, hα, hinv⟩ := hY.radii t
    refine ⟨α, hα, ?_⟩
    by_cases hne : ∃ p : X, p.val.2 = t
    · obtain ⟨p₀, hp₀⟩ := hne
      have he : vfFibre X.carrier t = {a | a + trAt f p₀ ∈ vfFibre Y.carrier t} := by
        ext a
        constructor
        · intro ha
          change (a, t) ∈ X.carrier at ha
          have hv := transl_value f hlab htr p₀ a (by rw [hp₀]; exact ha)
          have hmem := (f ⟨(a, p₀.val.2), by rw [hp₀]; exact ha⟩).property
          rw [hv, hlab, hp₀] at hmem
          exact hmem
        · intro ha
          change (a + trAt f p₀, t) ∈ Y.carrier at ha
          obtain ⟨p, hp⟩ := hf.2 ⟨_, ha⟩
          have hpt : p.val.2 = t := by
            have := congrArg (fun z : Y => z.val.2) hp
            simp only at this
            rw [hlab] at this
            exact this
          have hv := transl_value f hlab htr p₀ p.val.1 (by rw [hp₀, ← hpt]; exact p.property)
          have hpe : (⟨(p.val.1, p₀.val.2), by rw [hp₀, ← hpt]; exact p.property⟩ : X) = p :=
            Subtype.ext (Prod.ext rfl (hp₀.trans hpt.symm))
          rw [hpe, hp] at hv
          have h1 := congrArg Prod.fst hv
          have hap : a = p.val.1 := add_right_cancel h1
          change (a, t) ∈ X.carrier
          rw [hap, ← hpt]
          exact p.property
      rw [he]
      exact alphaInvariant_translate hinv _
    · have he : vfFibre X.carrier t = ∅ :=
        Set.eq_empty_of_forall_notMem fun a ha => hne ⟨⟨(a, t), ha⟩, rfl⟩
      rw [he]
      intro a b _
      exact Iff.rfl

end TranslInvariant

/-! ### The pulled-back first-stage set -/

section PullSet
variable {T : LRV.Substructure M} {m r : ℕ} {A : DefSet (rawMixedSpace (M := M) (m + 1 + 1) r) (T : Set M)}
  {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} (D : PrepContr (G := G) A ω)

namespace PrepContr

/-- The first stage of the contraction of `D`. -/
abbrev st : StandardContractionStage (G := G) D.Y := headStage D.C.data.program

/-- `p ↦ (init p, labels of st(prep p))`. -/
def psi : Map A (DefSet.univ (rawMixedSpace (M := M) (m + 1) D.st.arity) (T : Set M)) :=
  (initLabels _).comp ((Map.id A).pair (D.st.lift.comp D.prep))

theorem psi_val (p : A) : (D.psi p).val = (Fin.init p.val.1, (D.st.lift (D.prep p)).val.2) := rfl

/-- **The pulled-back first-stage set.** -/
abbrev pullSet' : DefSet (rawMixedSpace (M := M) (m + 1) D.st.arity) (T : Set M) := D.psi.image

theorem prep_labels_eq (p : A) : (D.prep p).val.2 = fun i => (D.st.lift (D.prep p)).val.2 (D.st.oldLabels i) :=
  funext fun i => (D.st.retained (D.prep p) i).symm

theorem prep_init (p : A) :
    Fin.init (D.prep p).val.1 = Fin.init p.val.1 + Fin.init (trAt D.prep p) := by
  funext i
  change (D.prep p).val.1 i.castSucc = p.val.1 i.castSucc + ((D.prep p).val.1 i.castSucc - p.val.1 i.castSucc)
  abel

theorem contraction_val (y : D.Y) :
    (D.st.contraction y).val = (Fin.init y.val.1, (D.st.lift y).val.2) := by
  rw [StandardContractionStage.contraction_value]
  refine Prod.ext ?_ rfl
  funext i
  exact D.st.relative y i

theorem trAt_eq_of_lift {p p' : A} (h : (D.st.lift (D.prep p)).val.2 = (D.st.lift (D.prep p')).val.2) :
    trAt D.prep p = trAt D.prep p' := by
  apply D.transl
  rw [prep_labels_eq, prep_labels_eq, h]

theorem psi_wd (p p' : A) (h : D.psi.toImage p = D.psi.toImage p') :
    (D.st.contraction.comp D.prep) p = (D.st.contraction.comp D.prep) p' := by
  have hv : (D.psi.toImage p).val = (D.psi.toImage p').val := congrArg Subtype.val h
  change (D.psi p).val = (D.psi p').val at hv
  rw [psi_val, psi_val] at hv
  obtain ⟨h1, h2⟩ := Prod.mk.inj hv
  apply Subtype.ext
  change (D.st.contraction (D.prep p)).val = (D.st.contraction (D.prep p')).val
  rw [contraction_val, contraction_val, prep_init, prep_init, h1, trAt_eq_of_lift D h2, h2]

theorem psi_surj : Function.Surjective D.psi.toImage := by
  rintro ⟨_, p, rfl⟩
  exact ⟨p, rfl⟩

/-- **The descended map `Ã → Y₁`.** -/
def prep₁ : Map D.pullSet' D.st.contracted :=
  definableSurjectiveDescent D.psi.toImage D.psi_surj (D.st.contraction.comp D.prep) D.psi_wd

theorem prep₁_apply (p : A) : D.prep₁ (D.psi.toImage p) = D.st.contraction (D.prep p) :=
  definableSurjectiveDescent_apply _ _ _ _ p

theorem prep₁_labels (x : D.pullSet') : (D.prep₁ x).val.2 = x.val.2 := by
  obtain ⟨p, rfl⟩ := D.psi_surj x
  rw [prep₁_apply, contraction_val]
  rfl

theorem prep₁_trAt (p : A) : trAt D.prep₁ (D.psi.toImage p) = Fin.init (trAt D.prep p) := by
  have h : (D.prep₁ (D.psi.toImage p)).val = (D.st.contraction (D.prep p)).val :=
    congrArg Subtype.val (D.prep₁_apply p)
  rw [contraction_val] at h
  funext i
  change (D.prep₁ (D.psi.toImage p)).val.1 i - (D.psi p).val.1 i = _
  rw [h, psi_val]
  rfl

theorem prep₁_transl (x x' : D.pullSet') (h : x.val.2 = x'.val.2) : trAt D.prep₁ x = trAt D.prep₁ x' := by
  obtain ⟨p, rfl⟩ := D.psi_surj x
  obtain ⟨p', rfl⟩ := D.psi_surj x'
  rw [prep₁_trAt, prep₁_trAt, trAt_eq_of_lift D h]

theorem prep₁_bijective : Function.Bijective D.prep₁ := by
  constructor
  · intro x x' he
    obtain ⟨p, rfl⟩ := D.psi_surj x
    obtain ⟨p', rfl⟩ := D.psi_surj x'
    rw [prep₁_apply, prep₁_apply] at he
    have hv := congrArg Subtype.val he
    rw [contraction_val, contraction_val] at hv
    obtain ⟨h1, h2⟩ := Prod.mk.inj hv
    rw [prep_init, prep_init, trAt_eq_of_lift D h2] at h1
    have h3 : Fin.init p.val.1 = Fin.init p'.val.1 := add_right_cancel h1
    apply Subtype.ext
    change (D.psi p).val = (D.psi p').val
    rw [psi_val, psi_val, h3, h2]
  · intro z
    obtain ⟨y, rfl⟩ := D.st.contraction_surjective z
    obtain ⟨p, rfl⟩ := D.homeo.bijective.2 y
    exact ⟨D.psi.toImage p, D.prep₁_apply p⟩

theorem mem_pullSet' (x : Mixed M (m + 1) D.st.arity) :
    x ∈ D.pullSet'.carrier ↔ ∃ p : A, (D.psi p).val = x := Iff.rfl

theorem pullSet'_vfBounded (hA : VFBounded A.carrier) : VFBounded D.pullSet'.carrier := by
  obtain ⟨γ, hγ⟩ := hA
  refine ⟨γ, ?_⟩
  rintro _ ⟨p, rfl⟩ i
  exact hγ p.val p.property i.castSucc

theorem pullSet'_proper (hA : VFBounded A.carrier) : ProperInvariant (T : Set M) D.pullSet'.carrier :=
  properInvariant_of_transl D.prep₁ D.prep₁_bijective D.prep₁_labels D.prep₁_transl D.st.contracted_proper
    (D.pullSet'_vfBounded hA)

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

/-- The form on the pulled-back first-stage set. -/
def ω₁ : Map D.pullSet' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)) :=
  (restForm D.C.data).comp D.prep₁

/-- **Prepared contraction data for the pulled-back first-stage set**: `prep₁`
followed by the rest of the contraction. -/
def rest (hA : VFBounded A.carrier) : PrepContr (G := G) D.pullSet' D.ω₁ where
  q := D.st.arity
  Y := D.st.contracted
  prep := D.prep₁
  homeo := transl_homeo D.prep₁ D.prep₁_labels D.prep₁_transl h00 hc hκ hs hv hsmall hΓ (D.pullSet'_proper hA)
    D.st.contracted_proper D.prep₁_bijective
  unit := transl_unit D.prep₁ D.prep₁_labels D.prep₁_transl hv (D.pullSet'_proper hA)
  oldIndex := id
  retained := fun p j => by rw [prep₁_labels]; rfl
  transl := fun x x' h => D.prep₁_transl x x' (by rwa [prep₁_labels, prep₁_labels] at h)
  θ := restForm D.C.data
  transport := fun _ => rfl
  C := restContraction h00 hc lin hκ hs hv hsmall hΓ D.C.data

/-! ### Hypotheses for the pulled-back first-stage sets -/

theorem pull_proj (b : Fin (m + 1) → VF M) :
    (∃ w, (b, w) ∈ D.pullSet'.carrier) ↔ ∃ p ∈ A.carrier, Fin.init p.1 = b := by
  constructor
  · rintro ⟨w, p, hp⟩
    have hp' : (D.psi p).val = (b, w) := hp
    rw [psi_val] at hp'
    exact ⟨p.val, p.property, congrArg Prod.fst hp'⟩
  · rintro ⟨p, hp, hb⟩
    refine ⟨(D.st.lift (D.prep ⟨p, hp⟩)).val.2, ⟨p, hp⟩, ?_⟩
    change (D.psi ⟨p, hp⟩).val = _
    rw [psi_val]
    exact Prod.ext hb rfl

variable {k : ℕ}

include h00 hc hκ hs hsmall in
theorem contracted_fin (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin (m + 1 + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    ∀ (b : Fin (m + 1) → VF M) (t : Fin (k + 1) → RVInfinity M),
      {u | (b, u) ∈ D.st.contracted.carrier ∧ u ∘ restLabelsOrdered D.C (D.oldIndex ∘ π) = t}.Finite := by
  intro b t
  have hT := unbundle_finite_n (head_start_finite_rv_fibres_of_bijective hc h00 hκ.le hs hsmall D.st.lift
    D.st.home.bijective k (D.oldIndex ∘ π) (D.st.oldLabels ∘ (D.oldIndex ∘ π)) (fun y i => D.st.retained y _)
    (D.finY hc h00 hκ hs hsmall π hFin))
  obtain ⟨x, hx⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) (fun _ : Fin 1 => t (Fin.last k))
  refine (hT (Fin.snoc b (x 0)) (t ∘ Fin.castSucc)).subset ?_
  rintro u ⟨hu, ht⟩
  refine ⟨(D.st.recover_target (Fin.snoc b (x 0), u)).mpr ⟨by simpa only [Fin.init_snoc] using hu, ?_⟩, ?_⟩
  · change rv M (Fin.snoc (α := fun _ => VF M) b (x 0) (Fin.last (m + 1))) = u D.st.leading
    rw [Fin.snoc_last]
    have h1 := congrFun hx 0
    have h2 := congrFun ht (Fin.last k)
    simp only [Function.comp_apply, restLabelsOrdered, Fin.snoc_last] at h2
    exact h1.trans h2.symm
  · funext j
    have h2 := congrFun ht j.castSucc
    simp only [Function.comp_apply, restLabelsOrdered, Fin.snoc_castSucc] at h2
    exact h2

include h00 hc hκ hs hsmall in
theorem pull_fin (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin (m + 1 + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    ∀ (b : Fin (m + 1) → VF M) (t : Fin (k + 1) → RVInfinity M),
      {u | (b, u) ∈ D.pullSet'.carrier ∧ u ∘ restLabelsOrdered D.C (D.oldIndex ∘ π) = t}.Finite := by
  have hinv : Function.Bijective (D.prep₁.inverse D.prep₁_bijective) :=
    ⟨fun y y' he => by simpa only [Map.apply_inverse] using congrArg D.prep₁ he,
      fun x => ⟨D.prep₁ x, Map.inverse_apply _ _ x⟩⟩
  exact unbundle_finite_n (head_start_finite_rv_fibres_of_bijective hc h00 hκ.le hs hsmall
    (D.prep₁.inverse D.prep₁_bijective) hinv (k + 1) (restLabelsOrdered D.C (D.oldIndex ∘ π))
    (restLabelsOrdered D.C (D.oldIndex ∘ π))
    (fun y i => by
      have h := D.prep₁_labels (D.prep₁.inverse D.prep₁_bijective y)
      rw [Map.apply_inverse] at h
      rw [← h])
    (D.contracted_fin h00 hc hκ hs hsmall π hFin))

theorem pull_nonzero (π : Fin k → Fin r) (hNZ : ∀ p ∈ A.carrier, ∀ i, (p.2 (π i)).val ≠ iRVZero) :
    ∀ x ∈ D.pullSet'.carrier, ∀ i, (x.2 (restLabelsOrdered D.C (D.oldIndex ∘ π) i)).val ≠ iRVZero := by
  rintro _ ⟨p, rfl⟩ i
  show ((D.psi p).val.2 (restLabelsOrdered D.C (D.oldIndex ∘ π) i)).val ≠ iRVZero
  rw [psi_val]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [restLabelsOrdered, Fin.snoc_last]
    have h := firstStage_nonzero D.C.data (D.st.contraction (D.prep p)).val (D.st.contraction (D.prep p)).property 0
    rw [contraction_val] at h
    exact h
  · simp only [restLabelsOrdered, Fin.snoc_castSucc, Function.comp_apply]
    rw [D.st.retained, D.retained]
    exact hNZ p.val p.property j

include h00 hc hκ hs hv hsmall hΓ in
/-- **First stage and rest for prepared data**: the head-start-`k` class of `D`
is the head-start-`(k + 1)` class of the rest data on the pulled-back
first-stage set. -/
theorem cls_rest (hA : VFBounded A.carrier) (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin (m + 1 + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    D.cls hc h00 hκ hs hsmall π hFin =
      castCls (show (m + 1) + (k + 1) = (m + 1 + 1) + k by omega)
        ((D.rest h00 hc hκ hs hv hsmall hΓ hA).cls hc h00 hκ hs hsmall (restLabelsOrdered D.C (D.oldIndex ∘ π))
          (D.pull_fin h00 hc hκ hs hsmall π hFin)) := by
  unfold PrepContr.cls
  rw [cls_headStart_rest_ordered h00 hc lin hκ hs hv hsmall hΓ D.C k (D.oldIndex ∘ π)
    (D.finY hc h00 hκ hs hsmall π hFin)]
  rfl

end PrepContr

end PullSet

end DiamondIntegral.Section7.Lemma714Reduce
