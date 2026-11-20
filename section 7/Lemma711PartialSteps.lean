import «section 7».Lemma711PartialClass

/-! Lemma 7.11 (`special:to:blowup:coa`) for partial lifts, part 2: head-start
chain sets along relative aperture chains.

Along a relative aperture chain `f : X → Y` on sets with `n` VF coordinates,
every head-start chain set on `X` transports, with carried labels and the
transported form, to one on `Y` whose class is reached from the class on `X`
by blowups (`claimHN_relative_chain`):

* regularization and zero-centred steps only retag, so they keep the class
  (`clsHN_regHGoodN`, `claimHN_zc`);
* a relative step is carried to the head-start bundle (Section 6
  `RelativeApertureData.carryHeadStart`), where Section 7's `step_rel` gives one
  blowup (`exists_step_rel`, which reads `step_rel` in any grade), and the image
  of the carried step is the bundle of the image (`carryHeadStart_image`);
* centripetal steps are relative steps (Section 6 `CentripetalData.relativeData`).

For `n = 1` this is `Lemma714Head.claimH_relative_chain`
(`claimH_of_claimHN`, `claimH_relative_chain_of_general`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma711Partial
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.SpecialChains DiamondIntegral.Section7.SpecialChainRel
open DiamondIntegral.Section7.SpecialChainInduction
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.Lemma714Head
open IntegrationInACVF.Section6.Iteration

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ### Unbundling -/

section Unbundle
variable {S : Set M} {n r k : ℕ} {Y : DefSet (rawMixedSpace (M := M) n r) S} {lab : Fin k → Fin r}

theorem lift_memN {p : Mixed M n r} (hp : p ∈ Y.carrier) :
    ∃ e : Fin k → VF M, ((Fin.append p.1 e, p.2) : Mixed M (n + k) r) ∈ (rvHeadStartBundle Y k lab).carrier := by
  obtain ⟨e, he⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) (p.2 ∘ lab)
  refine ⟨e, (mem_rvHeadStartBundle Y k lab _ _).mpr ?_⟩
  rw [headStartBaseVF_append, headStartExtraVF_append]
  exact ⟨hp, he⟩

theorem unbundle_pullbackN (hB : IsRVPullback (rvHeadStartBundle Y k lab).carrier) : IsRVPullback Y.carrier := by
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨p, hp, h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
    obtain ⟨e, he⟩ := lift_memN (lab := lab) hp
    have hQ : ((Fin.append q.1 e, q.2) : Mixed M (n + k) r) ∈ (rvHeadStartBundle Y k lab).carrier := by
      rw [← hB]
      refine (mem_rvHull_iff _ _).mpr ⟨_, he, ?_, h2⟩
      change tupleRV M (Fin.append p.1 e) = tupleRV M (Fin.append q.1 e)
      have hpq : (fun i => rv M (p.1 i)) = fun i => rv M (q.1 i) := h1
      funext i
      refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simp only [DiamondIntegral.Section2.tupleRV, Fin.append_left]
        exact congrFun hpq l
      · simp only [DiamondIntegral.Section2.tupleRV, Fin.append_right]
    have := ((mem_rvHeadStartBundle Y k lab _ _).mp hQ).1
    rwa [headStartBaseVF_append] at this
  · exact subset_rvHull _

theorem unbundle_finiteN (hB : ∀ a : Fin (n + k) → VF M, {u : Fin r → RVInfinity M |
      (a, u) ∈ (rvHeadStartBundle Y k lab).carrier}.Finite) :
    ∀ (a : Fin n → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ Y.carrier ∧ u ∘ lab = t}.Finite := by
  intro a t
  obtain ⟨e, he⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) t
  apply (hB (Fin.append a e)).subset
  rintro u ⟨hu, hl⟩
  apply (mem_rvHeadStartBundle Y k lab _ _).mpr
  rw [headStartBaseVF_append, headStartExtraVF_append, he, hl]
  exact ⟨hu, rfl⟩

theorem unbundle_vfBoundedN (hB : VFDoublyBounded (rvHeadStartBundle Y k lab).carrier) :
    VFDoublyBounded Y.carrier := by
  obtain ⟨γ, hγ⟩ := hB
  refine ⟨γ, fun p hp i => ?_⟩
  obtain ⟨e, he⟩ := lift_memN (lab := lab) hp
  have := hγ _ he (Fin.castAdd k i)
  simpa only [Fin.append_left] using this

theorem unbundle_rvBoundedN (hB : RVSupportDoublyBounded (rvHeadStartBundle Y k lab).carrier) :
    RVSupportDoublyBounded Y.carrier := by
  obtain ⟨γ, hγ⟩ := hB
  refine ⟨γ, fun p hp i => ?_⟩
  obtain ⟨e, he⟩ := lift_memN (lab := lab) hp
  exact hγ _ he i

end Unbundle

/-! ### The claim along a map -/

section Claims
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M}

/-- Transport of a head-start chain set along an equality of sets. -/
def HGoodN.transport {n r k : ℕ} {X X' : DefSet (rawMixedSpace (M := M) n r) (T : Set M)} {lab : Fin k → Fin r}
    (h : X = X') (g : HGoodN X lab) : HGoodN X' lab := h ▸ g

theorem HGoodN.transport_form {n r k : ℕ} {X X' : DefSet (rawMixedSpace (M := M) n r) (T : Set M)}
    {lab : Fin k → Fin r} (h : X = X') (g : HGoodN X lab) (p : X) :
    (g.transport h).form ⟨p.val, h ▸ p.property⟩ = g.form p := by
  subst h
  rfl

theorem clsHN_transport {n r k : ℕ} {X X' : DefSet (rawMixedSpace (M := M) n r) (T : Set M)}
    {lab : Fin k → Fin r} (h : X = X') (g : HGoodN X lab) : clsHN hc (g.transport h) = clsHN hc g := by
  subst h
  rfl

variable (k : ℕ)

/-- The conclusion of the partial-lift Lemma 7.11 along `f : A → B`: every
head-start chain set on `A` transports, with carried labels and the transported
form, to one on `B` whose class is reached from the class on `A` by blowups. -/
def ClaimHN {n r s : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) (T : Set M))
    (B : DefSet (rawMixedSpace (M := M) n s) (T : Set M)) (f : Map A B) : Prop :=
  ∀ (lab : Fin k → Fin r) (g : HGoodN A lab), ∃ lab' : Fin k → Fin s,
    (∀ p : A, ∀ i, (f p).val.2 (lab' i) = p.val.2 (lab i)) ∧
    ∃ g' : HGoodN B lab', (∀ p : A, g'.form (f p) = g.form p) ∧ Reached (clsHN hc g) (clsHN hc g')

variable {k}

theorem claimHN_comp {n r s t : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n s) (T : Set M)} {C : DefSet (rawMixedSpace (M := M) n t) (T : Set M)}
    {f : Map A B} {g : Map B C} (hf : ClaimHN hc k A B f) (hg : ClaimHN hc k B C g) :
    ClaimHN hc k A C (g.comp f) := by
  intro lab g0
  obtain ⟨lab1, hL1, g1, hf1, hs1⟩ := hf lab g0
  obtain ⟨lab2, hL2, g2, hf2, hs2⟩ := hg lab1 g1
  exact ⟨lab2, fun p i => (hL2 (f p) i).trans (hL1 p i), g2, fun p => (hf2 (f p)).trans (hf1 p), hs1.trans hs2⟩

/-- The identity keeps every head-start chain set. -/
theorem claimHN_id {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) (T : Set M)) :
    ClaimHN hc k A A (Map.id A) :=
  fun lab g => ⟨lab, fun _ _ => rfl, g, fun _ => rfl, Reached.refl _⟩

/-! #### Regularization -/

section Reg
variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) (T : Set M)} {lab : Fin k → Fin r}

/-- The regularization of a head-start chain set. -/
def regHGoodN (g : HGoodN A lab) : HGoodN (regularizeMap A).image (Fin.natAdd n ∘ lab) where
  pullback := regularize_pullback A g.pullback
  finite := by
    intro a t
    apply ((g.finite a t).image (fun u => (regularize ((a, u) : Mixed M n r)).2)).subset
    rintro u' ⟨hu', hl⟩
    obtain ⟨p, hp, he⟩ := (mem_regularize A).mp hu'
    have h1 : p.1 = a := congrArg Prod.fst he
    have hpe : ((a, p.2) : Mixed M n r) = p := Prod.ext h1.symm rfl
    have h2 : (regularize p).2 = u' := congrArg Prod.snd he
    refine ⟨p.2, ⟨hpe ▸ hp, ?_⟩, ?_⟩
    · funext i
      have := congrFun hl i
      simp only [Function.comp_apply] at this ⊢
      rw [← h2, regularize_snd_right] at this
      exact this
    · show (regularize ((a, p.2) : Mixed M n r)).2 = u'
      rw [hpe]
      exact h2
  vfBounded := regularize_vfDoublyBounded A g.vfBounded
  rvBounded := by
    obtain ⟨γ, hγ⟩ := g.vfBounded
    obtain ⟨δ, hδ⟩ := g.rvBounded
    have h1 : ((max γ δ)⁻¹).val ≤ (γ⁻¹).val := show (max γ δ)⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left _ _)
    have h2 : ((max γ δ)⁻¹).val ≤ (δ⁻¹).val := show (max γ δ)⁻¹ ≤ δ⁻¹ from inv_le_inv' (le_max_right _ _)
    have h3 : γ.val ≤ (max γ δ).val := show γ ≤ max γ δ from le_max_left _ _
    have h4 : δ.val ≤ (max γ δ).val := show δ ≤ max γ δ from le_max_right _ _
    refine ⟨max γ δ, fun p hp i => ?_⟩
    obtain ⟨q, hq, rfl⟩ := (mem_regularize A).mp hp
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [regularize_snd_left]
      obtain ⟨hl, hu⟩ := hγ q hq i
      exact ⟨h1.trans hl, hu.trans h3⟩
    · rw [regularize_snd_right]
      obtain ⟨hl, hu⟩ := hδ q hq i
      exact ⟨h2.trans hl, hu.trans h4⟩
  form := g.form.comp ((regularization A).inverse (regularization_bijective A))
  form_labels := by
    intro p q he
    obtain ⟨a, rfl⟩ := (regularization_bijective A).2 p
    obtain ⟨b, rfl⟩ := (regularization_bijective A).2 q
    change g.form ((regularization A).inverse _ (regularization A a)) =
      g.form ((regularization A).inverse _ (regularization A b))
    rw [Map.inverse_apply, Map.inverse_apply]
    exact g.form_labels a b (regularize_snd_eq.mp he).2

theorem regHGoodN_form (g : HGoodN A lab) (p : A) : (regHGoodN g).form (regularization A p) = g.form p := by
  change g.form ((regularization A).inverse _ (regularization A p)) = _
  rw [Map.inverse_apply]

/-- **Regularization keeps the head-start class.** -/
theorem clsHN_regHGoodN (g : HGoodN A lab) : clsHN hc (regHGoodN g) = clsHN hc g := by
  have hL : ∀ p : A, ∀ i, (regularization A p).val.2 ((Fin.natAdd n ∘ lab) i) = p.val.2 (lab i) :=
    fun p i => regularize_snd_right p.val (lab i)
  let H := carryHeadStartBijection (regularization A) (regularization_bijective A) k lab (Fin.natAdd n ∘ lab) hL
  let W := rvHeadStartBundle A k lab
  let RW := regularization W
  have hRW := regularization_bijective W
  let Φ : Map (regularizeMap W).image (rvHeadStartBundle (regularizeMap A).image k (Fin.natAdd n ∘ lab)) :=
    H.map.comp (RW.inverse hRW)
  have hΦ : ∀ z : W, Φ (RW z) = H.map z := by
    intro z
    change H.map (RW.inverse hRW (RW z)) = _
    rw [Map.inverse_apply]
  have hfst : ∀ z : W, (H.map z).val.1 = z.val.1 :=
    carried_fstN (regularization A) (regularization_bijective A) (fun _ => rfl) hL
  have htags : ∀ z : W, (H.map z).val.2 = (regularize (headStartBaseVF n k z.val.1, z.val.2)).2 := by
    intro z
    rw [H.labels z]
    change (regularize (headStartBaseProjection A k lab z).val).2 = _
    rw [headStartBaseProjection_value]
  have hextra : ∀ z : W, tupleRV M (headStartExtraVF n k z.val.1) = z.val.2 ∘ lab :=
    fun z => ((mem_rvHeadStartBundle A k lab z.val.1 z.val.2).mp z.property).2
  have hbij : Function.Bijective Φ := by
    refine H.bijective.comp ⟨fun a b h => ?_, fun x => ⟨RW x, by rw [Map.inverse_apply]⟩⟩
    obtain ⟨x, rfl⟩ := hRW.2 a
    obtain ⟨y, rfl⟩ := hRW.2 b
    rw [Map.inverse_apply, Map.inverse_apply] at h
    rw [h]
  symm
  change clsG hc (bundleGoodN g) = clsG hc (bundleGoodN (regHGoodN g))
  rw [← clsG_reg hc (bundleGoodN g)]
  refine clsG_eq_of_wholeFibres hc (regGood (bundleGoodN g)) (bundleGoodN (regHGoodN g)) Φ hbij ?_ ?_ ?_
  · apply wholeFibres_of_tags Φ hbij
    intro a b
    obtain ⟨z, rfl⟩ := hRW.2 a
    obtain ⟨w, rfl⟩ := hRW.2 b
    rw [hΦ, hΦ, htags, htags]
    change (regularize (headStartBaseVF n k z.val.1, z.val.2)).2 = (regularize (headStartBaseVF n k w.val.1, w.val.2)).2 ↔
      (regularize z.val).2 = (regularize w.val).2
    rw [regularize_snd_eq, regularize_snd_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      apply headStart_vf_ext k
      · change headStartBaseVF n k (rv M ∘ z.val.1) = headStartBaseVF n k (rv M ∘ w.val.1)
        rw [headStartBaseVF_comp, headStartBaseVF_comp]
        exact h1
      · change headStartExtraVF n k (rv M ∘ z.val.1) = headStartExtraVF n k (rv M ∘ w.val.1)
        rw [headStartExtraVF_comp, headStartExtraVF_comp]
        change tupleRV M (headStartExtraVF n k z.val.1) = tupleRV M (headStartExtraVF n k w.val.1)
        rw [hextra, hextra]
        simp only at h2
        rw [h2]
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      change rv M ∘ headStartBaseVF n k z.val.1 = rv M ∘ headStartBaseVF n k w.val.1
      rw [← headStartBaseVF_comp, ← headStartBaseVF_comp]
      exact congrArg (headStartBaseVF n k) h1
  · intro a
    obtain ⟨z, rfl⟩ := hRW.2 a
    rw [hΦ, hfst]
    rfl
  · intro a
    obtain ⟨z, rfl⟩ := hRW.2 a
    rw [hΦ]
    change (regHGoodN g).form (headStartBaseProjection _ k _ (H.map z)) = regForm (bundleGoodN g) (RW z)
    rw [regForm_apply, H.base z, regHGoodN_form]
    rfl

end Reg

/-- **A regularization step** for head-start chain sets. -/
theorem claimHN_regularize {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) (T : Set M)) :
    ClaimHN hc k A (regularizeMap A).image (regularization A) := by
  intro lab g
  refine ⟨Fin.natAdd n ∘ lab, fun p i => regularize_snd_right p.val (lab i), regHGoodN g, regHGoodN_form g, ?_⟩
  rw [clsHN_regHGoodN]
  exact Reached.refl _

/-! #### Zero-centred steps -/

section ZC
variable (h00 : M ⊨ Axioms.ACVF00)
variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) (T : Set M)} {lab : Fin k → Fin r}

theorem mem_zcImageN (g : HGoodN A lab) (Z : ZeroCenteredData A) {q : Mixed M n (n + r)} :
    q ∈ Z.map.image.carrier ↔
      ∃ p ∈ A.carrier, q = (p.1, Fin.append (fun _ : Fin n => branchTag (M := M) false) p.2) := by
  rw [ZeroCenteredData.image_carrier]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, zc_point Z g.vfBounded hp⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, zc_point Z g.vfBounded hp⟩

include h00 in
/-- The image of a zero-centred step of a head-start chain set. -/
def zcHGoodN (g : HGoodN A lab) (Z : ZeroCenteredData A) : HGoodN Z.map.image (Fin.natAdd n ∘ lab) where
  pullback := by
    show rvHull _ = _
    apply Set.Subset.antisymm
    · intro q hq
      obtain ⟨q', hq', h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
      obtain ⟨p, hp, rfl⟩ := (mem_zcImageN g Z).mp hq'
      apply (mem_zcImageN g Z).mpr
      refine ⟨(q.1, p.2), rvPullback_mem_of_sameRV g.pullback hp h1 rfl, ?_⟩
      exact Prod.ext rfl h2.symm
    · intro q hq
      exact (mem_rvHull_iff _ q).mpr ⟨q, hq, rfl, rfl⟩
  finite := by
    intro a t
    apply ((g.finite a t).image (fun u => Fin.append (fun _ : Fin n => branchTag (M := M) false) u)).subset
    rintro v ⟨hv, hl⟩
    obtain ⟨p, hp, he⟩ := (mem_zcImageN g Z).mp hv
    have h1 : p.1 = a := (congrArg Prod.fst he).symm
    have h2 : v = Fin.append (fun _ : Fin n => branchTag (M := M) false) p.2 := congrArg Prod.snd he
    refine ⟨p.2, ⟨?_, ?_⟩, h2.symm⟩
    · change (a, p.2) ∈ A.carrier
      rw [← h1]
      exact hp
    · funext i
      have := congrFun hl i
      rw [h2] at this
      simpa only [Function.comp_apply, Fin.append_right] using this
  vfBounded := by
    obtain ⟨γ, hγ⟩ := g.vfBounded
    refine ⟨γ, fun q hq i => ?_⟩
    obtain ⟨p, hp, rfl⟩ := (mem_zcImageN g Z).mp hq
    exact hγ p hp i
  rvBounded := by
    obtain ⟨δ, hδ⟩ := g.rvBounded
    have h1 : ((max δ 1)⁻¹).val ≤ (δ⁻¹).val := show (max δ 1)⁻¹ ≤ δ⁻¹ from inv_le_inv' (le_max_left _ _)
    have h2 : δ.val ≤ (max δ 1).val := show δ ≤ max δ 1 from le_max_left _ _
    have h3 : ((max δ 1)⁻¹).val ≤ (1 : Values.Gamma (M := M)).val :=
      show (max δ 1)⁻¹ ≤ 1 from inv_le_one'.mpr (le_max_right _ _)
    have h4 : (1 : Values.Gamma (M := M)).val ≤ (max δ 1).val := show 1 ≤ max δ 1 from le_max_right _ _
    refine ⟨max δ 1, fun q hq i => ?_⟩
    obtain ⟨p, hp, rfl⟩ := (mem_zcImageN g Z).mp hq
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · change ((max δ 1)⁻¹).val ≤ Values.vrv (Fin.append (fun _ : Fin n => branchTag (M := M) false) p.2 (Fin.castAdd r i)) ∧
        Values.vrv (Fin.append (fun _ : Fin n => branchTag (M := M) false) p.2 (Fin.castAdd r i)) ≤ (max δ 1).val
      rw [Fin.append_left, branchTag_value]
      exact ⟨h3, h4⟩
    · change ((max δ 1)⁻¹).val ≤ Values.vrv (Fin.append (fun _ : Fin n => branchTag (M := M) false) p.2 (Fin.natAdd n i)) ∧
        Values.vrv (Fin.append (fun _ : Fin n => branchTag (M := M) false) p.2 (Fin.natAdd n i)) ≤ (max δ 1).val
      rw [Fin.append_right]
      obtain ⟨hl, hu⟩ := hδ p hp i
      exact ⟨h1.trans hl, hu.trans h2⟩
  form := g.form.comp (Z.bijection.inverse (Z.bijective h00))
  form_labels := by
    intro p q he
    obtain ⟨a, rfl⟩ := (Z.bijective h00).2 p
    obtain ⟨b, rfl⟩ := (Z.bijective h00).2 q
    change g.form (Z.bijection.inverse _ (Z.bijection a)) = g.form (Z.bijection.inverse _ (Z.bijection b))
    rw [Map.inverse_apply, Map.inverse_apply]
    apply g.form_labels
    have ha : (Z.bijection a).val = Z.point a.val := rfl
    have hb : (Z.bijection b).val = Z.point b.val := rfl
    rw [ha, hb, zc_point Z g.vfBounded a.property, zc_point Z g.vfBounded b.property] at he
    exact append_ones_injective he

theorem zcHGoodN_form (g : HGoodN A lab) (Z : ZeroCenteredData A) (p : A) :
    (zcHGoodN h00 g Z).form (Z.bijection p) = g.form p := by
  change g.form (Z.bijection.inverse _ (Z.bijection p)) = _
  rw [Map.inverse_apply]

include h00 in
/-- **A zero-centred step keeps the head-start class.** -/
theorem claimHN_zc (Z : ZeroCenteredData A) : ClaimHN hc k A Z.map.image Z.bijection := by
  intro lab g
  have hpt : ∀ p : A, (Z.bijection p).val = (p.val.1, Fin.append (fun _ : Fin n => branchTag (M := M) false) p.val.2) :=
    fun p => zc_point Z g.vfBounded p.property
  have hL : ∀ p : A, ∀ i, (Z.bijection p).val.2 ((Fin.natAdd n ∘ lab) i) = p.val.2 (lab i) := by
    intro p i
    rw [hpt]
    simp only [Function.comp_apply, Fin.append_right]
  refine ⟨Fin.natAdd n ∘ lab, hL, zcHGoodN h00 g Z, zcHGoodN_form h00 g Z, ?_⟩
  rw [clsHN_eq_of_retag hc g (zcHGoodN h00 g Z) Z.bijection (Z.bijective h00) ?_ (fun p => by rw [hpt]) hL
    (zcHGoodN_form h00 g Z)]
  · exact Reached.refl _
  · apply wholeFibres_of_tags Z.bijection (Z.bijective h00)
    intro p q
    rw [hpt, hpt]
    exact ⟨fun h => append_ones_injective h, fun h => by simp only at h ⊢; rw [h]⟩

end ZC

end Claims

/-! ### Relative steps and chains -/

section Rel
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {k : ℕ}
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hsmall : Cardinal.mk (T : Set M) < κ)

include hκ hs hsmall h00 in
/-- **Lemma 7.11 for one relative step, in any VF dimension `N`**: the image of
a chain set under relative aperture data, with the transported form, is a chain
set whose class is a blowup of length one of the class of the source
(`SpecialChainRel.step_rel`, read in the grade `N = 1 + d`; `N` is positive
because the data change a coordinate). -/
theorem exists_step_rel {N r : ℕ} {X : DefSet (rawMixedSpace (M := M) N r) (T : Set M)} (g : Good T X)
    (R : RelativeApertureData (G := G) X) :
    ∃ g' : Good T R.map.image, (∀ x : X, g'.form (R.bijection x) = g.form x) ∧
      Reached (clsG hc g) (clsG hc g') := by
  obtain ⟨d, rfl⟩ : ∃ d, N = 1 + d := ⟨N - 1, by have := R.coordinate.pos; omega⟩
  exact ⟨imageGood hc g R hκ hs hsmall h00, imageGood_form hc g R hκ hs hsmall h00,
    Reached.of_step (step_rel hc g R hκ hs hsmall h00)⟩

theorem relPoint_tailN {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) (T : Set M)}
    (R : RelativeApertureData (G := G) A) (x : A) :
    (fun i => (R.bijection x).val.2 (Fin.natAdd 1 i)) = x.val.2 := by
  funext i
  rw [RelativeApertureData.bijection_apply]
  simp only [RelativeApertureData.point, Fin.append_right]

include h00 hκ hs hv hsmall in
/-- **A relative step on a head-start chain set is one blowup** (carried to
the head-start bundle, Section 7's `step_rel`). -/
theorem claimHN_rel {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) (T : Set M)}
    (R : RelativeApertureData (G := G) A) : ClaimHN hc k A R.map.image R.bijection := by
  intro lab g
  let Rk := R.carryHeadStart h00 hc hκ hs hv k lab
  obtain ⟨Ig, hIg, hreach⟩ := exists_step_rel hc h00 hκ hs hsmall (bundleGoodN g) Rk
  have hE : Rk.map.image = rvHeadStartBundle R.map.image k (Fin.natAdd 1 ∘ lab) :=
    defSet_eq_of_carrier_eq (R.carryHeadStart_image h00 hc hκ hs hv k lab)
  let Ib := transport hE Ig
  have hL : ∀ p : A, ∀ i, (R.bijection p).val.2 ((Fin.natAdd 1 ∘ lab) i) = p.val.2 (lab i) := by
    intro p i
    exact congrFun (relPoint_tailN R p) (lab i)
  let g' : HGoodN R.map.image (Fin.natAdd 1 ∘ lab) :=
    { pullback := unbundle_pullbackN Ib.pullback
      finite := unbundle_finiteN Ib.finite
      vfBounded := unbundle_vfBoundedN Ib.vfBounded
      rvBounded := unbundle_rvBoundedN Ib.rvBounded
      form := g.form.comp (R.bijection.inverse (R.bijective h00))
      form_labels := by
        intro p q he
        obtain ⟨a, rfl⟩ := (R.bijective h00).2 p
        obtain ⟨b, rfl⟩ := (R.bijective h00).2 q
        change g.form (R.bijection.inverse _ (R.bijection a)) = g.form (R.bijection.inverse _ (R.bijection b))
        rw [Map.inverse_apply, Map.inverse_apply]
        apply g.form_labels
        rw [← relPoint_tailN R a, ← relPoint_tailN R b, he] }
  have hform' : ∀ p : A, g'.form (R.bijection p) = g.form p := by
    intro p
    change g.form (R.bijection.inverse _ (R.bijection p)) = _
    rw [Map.inverse_apply]
  refine ⟨Fin.natAdd 1 ∘ lab, hL, g', hform', ?_⟩
  have hcls : clsG hc Ig = clsHN hc g' := by
    apply clsG_congr hc hE Ig (bundleGoodN g')
    intro p
    obtain ⟨z, rfl⟩ := (Rk.bijective h00).2 p
    rw [hIg]
    change g'.form (headStartBaseProjection R.map.image k (Fin.natAdd 1 ∘ lab) ⟨(Rk.bijection z).val, _⟩) =
      g.form (headStartBaseProjection A k lab z)
    have hproj : headStartBaseProjection R.map.image k (Fin.natAdd 1 ∘ lab)
        ⟨(Rk.bijection z).val, hE ▸ (Rk.bijection z).property⟩ =
        R.bijection (headStartBaseProjection A k lab z) := by
      apply Subtype.ext
      rw [headStartBaseProjection_value, RelativeApertureData.bijection_apply,
        RelativeApertureData.bijection_apply, headStartBaseProjection_value]
      exact R.carryHeadStart_point h00 hc hκ hs hv k lab z.val z.property
    rw [hproj, hform']
  rw [← hcls]
  exact hreach

include h00 hκ hs hv hsmall in
/-- A step given by relative data with the same point map. -/
theorem claimHN_of_point {n r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n s) (T : Set M)} (f : Map A B) (hs1 : s = 1 + r)
    (R : RelativeApertureData (G := G) A) (hB : B.carrier = hs1 ▸ R.map.image.carrier)
    (hf : ∀ p : A, (f p).val = hs1 ▸ R.point p.val) : ClaimHN hc k A B f := by
  subst hs1
  have hE : R.map.image = B := DefSet.eq_of_carrier_eq hB.symm
  intro lab g
  obtain ⟨lab', hL, g', hform, hm⟩ := claimHN_rel hc h00 hκ hs hv hsmall R lab g
  have hfp : ∀ p : A, f p = ⟨(R.bijection p).val, hE ▸ (R.bijection p).property⟩ := fun p => Subtype.ext (hf p)
  refine ⟨lab', fun p i => ?_, g'.transport hE, fun p => ?_, ?_⟩
  · rw [hfp p]
    exact hL p i
  · rw [hfp p, HGoodN.transport_form, hform]
  · rw [clsHN_transport]
    exact hm

include h00 hκ hs hv hsmall in
/-- **The partial-lift Lemma 7.11 along special covariant chains.** -/
theorem claimHN_special {n r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n s) (T : Set M)} {f : Map A B}
    (h : SpecialCovariantChain (G := G) A B f) : ClaimHN hc k A B f := by
  induction h with
  | identity A _ => exact claimHN_id hc A
  | regularize A _ _ => exact claimHN_regularize hc A
  | centripetal A D =>
    exact claimHN_of_point hc h00 hκ hs hv hsmall D.bijection rfl D.relativeData
      (by rw [RelativeApertureData.image_carrier, CentripetalData.image_carrier]
          ext q
          constructor
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, hp, D.relativeData_point ⟨p, hp⟩⟩
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, hp, (D.relativeData_point ⟨p, hp⟩).symm⟩)
      (fun p => (D.relativeData_point p).symm)
  | zeroCentered A D => exact claimHN_zc hc h00 D
  | comp _ _ ihf ihg => exact claimHN_comp hc ihf ihg

include h00 hκ hs hv hsmall in
/-- **Lemma 7.11 (`special:to:blowup:coa`) for head-start chain sets with `n`
VF coordinates, along relative aperture chains.** For a relative aperture chain
`f : A → B` (a special covariant bijection acting on the `n` lifted
coordinates), every head-start chain set on `A` with labels `λ` transports to a
head-start chain set on `B`, with labels `λ'` carried by `f` and the
transported form, whose class (grade `n + k`) is reached from the class on `A`
by a blowup chain. -/
theorem claimHN_relative_chain {n r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n s) (T : Set M)} {f : Map A B}
    (h : RelativeApertureChain (G := G) A B f) : ClaimHN hc k A B f := by
  induction h with
  | original h => exact claimHN_special hc h00 hκ hs hv hsmall h
  | relative A D => exact claimHN_rel hc h00 hκ hs hv hsmall D
  | comp _ _ ihf ihg => exact claimHN_comp hc ihf ihg

/-! #### One VF coordinate -/

/-- For `n = 1`, the claim is the unary head-start claim of Lemma 7.14. -/
theorem claimH_of_claimHN {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)} {f : Map A B} (h : ClaimHN hc k A B f) :
    ClaimH hc k A B f := by
  intro lab g
  obtain ⟨lab', hL, g', hform, hm⟩ := h lab (HGoodN.ofH g)
  exact ⟨lab', hL, g'.toH, hform, reached_iff.mp hm⟩

include h00 hκ hs hv hsmall in
/-- `Lemma714Head.claimH_relative_chain` is the case `n = 1` of
`claimHN_relative_chain`. -/
theorem claimH_relative_chain_of_general {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)} {f : Map A B}
    (h : RelativeApertureChain (G := G) A B f) : ClaimH hc k A B f :=
  claimH_of_claimHN hc (claimHN_relative_chain hc h00 hκ hs hv hsmall h)

end Rel

end DiamondIntegral.Section7.Lemma711Partial
