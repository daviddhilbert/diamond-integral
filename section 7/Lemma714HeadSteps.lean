import «section 7».Lemma714HeadClass

/-! Lemma 7.14, part 15: Lemma 7.11 for head-start chain sets.

Along a relative aperture chain on unary sets that carries the head-start
labels, the head-start class is reached by blowups (`claimH_relative_chain`):

* regularization and zero-centred steps only retag, so they keep the class;
* a relative step is carried to the head-start bundle (`carryHeadStart`), where
  Section 7's `step_rel` gives one blowup, and the image of the carried step is
  the bundle of the image (`carryHeadStart_image`);
* centripetal steps are relative steps (Section 6 `CentripetalData.relativeData`).

This is the head-start form of Lemma 7.11 needed by the head-start Lemma 7.13. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

/-! ### Relative aperture data on head-start bundles -/

namespace DiamondIntegral.Section6.RelativeApertureData
open DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

/-- **Relative aperture data carried to a head-start bundle.** -/
def carryHeadStart (D : RelativeApertureData (G := G) A) :
    (k : ℕ) → (π : Fin k → Fin r) → RelativeApertureData (G := G) (rvHeadStartBundle A k π)
  | 0, _ => D
  | k + 1, π => (carryHeadStart D k (π ∘ Fin.castSucc)).carryBundle (π (Fin.last k))
      (rvCoordinateBundle_properInvariant h00 hc hκ hs hv _ _
        (rvHeadStartBundle_properInvariant h00 hc hκ hs hv A k _ D.sourceProper))

theorem rvCoordinateBundle_carrier_congr {B C : DefSet (rawMixedSpace (M := M) n r) S}
    (h : B.carrier = C.carrier) (j : Fin r) :
    (rvCoordinateBundle B j).carrier = (rvCoordinateBundle C j).carrier := by
  have : B = C := defSet_eq_of_carrier_eq h
  subst this
  rfl

theorem carryHeadStart_image (D : RelativeApertureData (G := G) A) :
    ∀ (k : ℕ) (π : Fin k → Fin r), (D.carryHeadStart h00 hc hκ hs hv k π).map.image.carrier =
      (rvHeadStartBundle D.map.image k (Fin.natAdd 1 ∘ π)).carrier
  | 0, _ => rfl
  | k + 1, π => by
    change ((D.carryHeadStart h00 hc hκ hs hv k (π ∘ Fin.castSucc)).carryBundle (π (Fin.last k)) _).map.image.carrier =
      (rvCoordinateBundle (rvHeadStartBundle D.map.image k ((Fin.natAdd 1 ∘ π) ∘ Fin.castSucc))
        (Fin.natAdd 1 (π (Fin.last k)))).carrier
    rw [carryBundle_image]
    exact rvCoordinateBundle_carrier_congr (carryHeadStart_image D k (π ∘ Fin.castSucc)) _

/-- The carried step acts as the original step on the base point. -/
theorem carryHeadStart_point (D : RelativeApertureData (G := G) A) :
    ∀ (k : ℕ) (π : Fin k → Fin r) (p : Mixed M (n + k) r), p ∈ (rvHeadStartBundle A k π).carrier →
      (headStartBaseVF n k ((D.carryHeadStart h00 hc hκ hs hv k π).point p).1,
        ((D.carryHeadStart h00 hc hκ hs hv k π).point p).2) = D.point (headStartBaseVF n k p.1, p.2)
  | 0, _, p, _ => rfl
  | k + 1, π, p, hp => by
    have hp' : p ∈ (rvCoordinateBundle (rvHeadStartBundle A k (π ∘ Fin.castSucc)) (π (Fin.last k))).carrier := hp
    change (headStartBaseVF n k (Fin.init (((D.carryHeadStart h00 hc hκ hs hv k (π ∘ Fin.castSucc)).carryBundle
        (π (Fin.last k)) _).point p).1), (((D.carryHeadStart h00 hc hκ hs hv k (π ∘ Fin.castSucc)).carryBundle
        (π (Fin.last k)) _).point p).2) = D.point (headStartBaseVF n k (Fin.init p.1), p.2)
    rw [carryBundle_point _ _ _ p hp', Fin.init_snoc]
    exact carryHeadStart_point D k (π ∘ Fin.castSucc) (Fin.init p.1, p.2) hp'.1

end DiamondIntegral.Section6.RelativeApertureData

namespace DiamondIntegral.Section7.Lemma714Head
open DiamondIntegral.Section6 DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ### Tuples and maps -/

section TupleMaps
variable {X Y : Type*} {n : ℕ}

omit [LRV.Structure M] hM in
theorem headStartBaseVF_comp (φ : X → Y) : ∀ (k : ℕ) (z : Fin (n + k) → X),
    headStartBaseVF n k (φ ∘ z) = φ ∘ headStartBaseVF n k z
  | 0, _ => rfl
  | k + 1, z => headStartBaseVF_comp φ k (Fin.init z)

omit [LRV.Structure M] hM in
theorem headStartExtraVF_comp (φ : X → Y) : ∀ (k : ℕ) (z : Fin (n + k) → X),
    headStartExtraVF n k (φ ∘ z) = φ ∘ headStartExtraVF n k z
  | 0, _ => Subsingleton.elim _ _
  | k + 1, z => by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [headStartExtraVF, Fin.lastCases_last, Function.comp_apply]
    · simp only [headStartExtraVF, Fin.lastCases_castSucc, Function.comp_apply]
      have := congrFun (headStartExtraVF_comp φ k (Fin.init z)) j
      exact this

end TupleMaps

/-- Whole label fibres from a correspondence of labels. -/
theorem wholeFibres_of_tags {S : Set M} {n r s : ℕ}
    {X : DefSet (rawMixedSpace (M := M) n r) S} {Y : DefSet (rawMixedSpace (M := M) n s) S}
    (F : Map X Y) (hF : Function.Bijective F)
    (h : ∀ p q : X, (F p).val.2 = (F q).val.2 ↔ p.val.2 = q.val.2) : MapsWholeTagFibres F := by
  intro p b
  constructor
  · intro hb
    obtain ⟨a, rfl⟩ := hF.2 b
    exact ⟨a, (h a p).mp hb, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (h a p).mpr ha

/-! ### Unbundling -/

section Unbundle
variable {S : Set M} {r k : ℕ} {Y : DefSet (rawMixedSpace (M := M) 1 r) S} {lab : Fin k → Fin r}

theorem lift_mem {p : Mixed M 1 r} (hp : p ∈ Y.carrier) :
    ∃ e : Fin k → VF M, ((Fin.append p.1 e, p.2) : Mixed M (1 + k) r) ∈ (rvHeadStartBundle Y k lab).carrier := by
  obtain ⟨e, he⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) (p.2 ∘ lab)
  refine ⟨e, (mem_rvHeadStartBundle Y k lab _ _).mpr ?_⟩
  rw [headStartBaseVF_append, headStartExtraVF_append]
  exact ⟨hp, he⟩

theorem unbundle_pullback (hB : IsRVPullback (rvHeadStartBundle Y k lab).carrier) : IsRVPullback Y.carrier := by
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨p, hp, h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
    obtain ⟨e, he⟩ := lift_mem (lab := lab) hp
    have hQ : ((Fin.append q.1 e, q.2) : Mixed M (1 + k) r) ∈ (rvHeadStartBundle Y k lab).carrier := by
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

theorem unbundle_finite (hB : ∀ a : Fin (1 + k) → VF M, {u : Fin r → RVInfinity M |
      (a, u) ∈ (rvHeadStartBundle Y k lab).carrier}.Finite) :
    ∀ (a : Fin 1 → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ Y.carrier ∧ u ∘ lab = t}.Finite := by
  intro a t
  obtain ⟨e, he⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) t
  apply (hB (Fin.append a e)).subset
  rintro u ⟨hu, hl⟩
  apply (mem_rvHeadStartBundle Y k lab _ _).mpr
  rw [headStartBaseVF_append, headStartExtraVF_append, he, hl]
  exact ⟨hu, rfl⟩

theorem unbundle_vfBounded (hB : VFDoublyBounded (rvHeadStartBundle Y k lab).carrier) :
    VFDoublyBounded Y.carrier := by
  obtain ⟨γ, hγ⟩ := hB
  refine ⟨γ, fun p hp i => ?_⟩
  obtain ⟨e, he⟩ := lift_mem (lab := lab) hp
  have := hγ _ he (Fin.castAdd k i)
  simpa only [Fin.append_left] using this

theorem unbundle_rvBounded (hB : RVSupportDoublyBounded (rvHeadStartBundle Y k lab).carrier) :
    RVSupportDoublyBounded Y.carrier := by
  obtain ⟨γ, hγ⟩ := hB
  refine ⟨γ, fun p hp i => ?_⟩
  obtain ⟨e, he⟩ := lift_mem (lab := lab) hp
  exact hγ _ he i

end Unbundle

/-! ### Head-start claims along chains -/

section Claims
open DiamondIntegral.Section7.SpecialChains DiamondIntegral.Section7.SpecialChainRel
open DiamondIntegral.Section7.SpecialChainInduction
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.LiftClasses
open IntegrationInACVF.Section6.Iteration
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M}

/-- Transport of a head-start chain set along an equality of sets. -/
def HGood.transport {r k : ℕ} {X X' : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)} {lab : Fin k → Fin r}
    (h : X = X') (g : HGood X lab) : HGood X' lab := h ▸ g

theorem HGood.transport_form {r k : ℕ} {X X' : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
    {lab : Fin k → Fin r} (h : X = X') (g : HGood X lab) (p : X) :
    (g.transport h).form ⟨p.val, h ▸ p.property⟩ = g.form p := by
  subst h
  rfl

theorem clsH_transport {r k : ℕ} {X X' : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)} {lab : Fin k → Fin r}
    (h : X = X') (g : HGood X lab) : clsH hc (g.transport h) = clsH hc g := by
  subst h
  rfl

variable (k : ℕ)

/-- The conclusion of the head-start Lemma 7.11 along `f : A → B`: every
head-start chain set on `A` transports, with carried labels, to one on `B` whose
class is a blowup of the class on `A`. -/
def ClaimH {r s : ℕ} (A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M))
    (B : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)) (f : Map A B) : Prop :=
  ∀ (lab : Fin k → Fin r) (g : HGood A lab), ∃ lab' : Fin k → Fin s,
    (∀ p : A, ∀ i, (f p).val.2 (lab' i) = p.val.2 (lab i)) ∧
    ∃ g' : HGood B lab', (∀ p : A, g'.form (f p) = g.form p) ∧ ∃ m, BlowupSteps m (clsH hc g) (clsH hc g')

variable {k}

theorem claimH_comp {r s t : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)} {C : DefSet (rawMixedSpace (M := M) 1 t) (T : Set M)}
    {f : Map A B} {g : Map B C} (hf : ClaimH hc k A B f) (hg : ClaimH hc k B C g) : ClaimH hc k A C (g.comp f) := by
  intro lab g0
  obtain ⟨lab1, hL1, g1, hf1, m1, hs1⟩ := hf lab g0
  obtain ⟨lab2, hL2, g2, hf2, m2, hs2⟩ := hg lab1 g1
  exact ⟨lab2, fun p i => (hL2 (f p) i).trans (hL1 p i), g2, fun p => (hf2 (f p)).trans (hf1 p), m1 + m2,
    hs1.trans hs2⟩

/-- The VF part is kept by a carried map of a VF-preserving map. -/
theorem carried_fst {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)} {lab : Fin k → Fin r} {lab' : Fin k → Fin s}
    (f : Map A B) (hf : Function.Bijective f) (hvf : ∀ p : A, (f p).val.1 = p.val.1)
    (hL : ∀ p : A, ∀ i, (f p).val.2 (lab' i) = p.val.2 (lab i)) (p : rvHeadStartBundle A k lab) :
    ((carryHeadStartBijection f hf k lab lab' hL).map p).val.1 = p.val.1 := by
  let H := carryHeadStartBijection f hf k lab lab' hL
  apply headStart_vf_ext k
  · have hbase := congrArg Subtype.val (H.base p)
    rw [headStartBaseProjection_value] at hbase
    have h1 : headStartBaseVF 1 k (H.map p).val.1 = (f (headStartBaseProjection A k lab p)).val.1 :=
      congrArg (fun z : Mixed M 1 s => z.1) hbase
    rw [h1, hvf, headStartBaseProjection_value]
  · exact H.fixed p

/-! #### Regularization -/

section Reg
variable {r : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)} {lab : Fin k → Fin r}

/-- The regularization of a head-start chain set. -/
def regHGood (g : HGood A lab) : HGood (regularizeMap A).image (Fin.natAdd 1 ∘ lab) where
  pullback := regularize_pullback A g.pullback
  finite := by
    intro a t
    apply ((g.finite a t).image (fun u => (regularize ((a, u) : Mixed M 1 r)).2)).subset
    rintro u' ⟨hu', hl⟩
    obtain ⟨p, hp, he⟩ := (mem_regularize A).mp hu'
    have h1 : p.1 = a := congrArg Prod.fst he
    have hpe : ((a, p.2) : Mixed M 1 r) = p := Prod.ext h1.symm rfl
    have h2 : (regularize p).2 = u' := congrArg Prod.snd he
    refine ⟨p.2, ⟨hpe ▸ hp, ?_⟩, ?_⟩
    · funext i
      have := congrFun hl i
      simp only [Function.comp_apply] at this ⊢
      rw [← h2, regularize_snd_right] at this
      exact this
    · show (regularize ((a, p.2) : Mixed M 1 r)).2 = u'
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

theorem regHGood_form (g : HGood A lab) (p : A) : (regHGood g).form (regularization A p) = g.form p := by
  change g.form ((regularization A).inverse _ (regularization A p)) = _
  rw [Map.inverse_apply]

/-- **Regularization keeps the head-start class.** -/
theorem clsH_regHGood (g : HGood A lab) : clsH hc (regHGood g) = clsH hc g := by
  have hL : ∀ p : A, ∀ i, (regularization A p).val.2 ((Fin.natAdd 1 ∘ lab) i) = p.val.2 (lab i) :=
    fun p i => regularize_snd_right p.val (lab i)
  let H := carryHeadStartBijection (regularization A) (regularization_bijective A) k lab (Fin.natAdd 1 ∘ lab) hL
  let W := rvHeadStartBundle A k lab
  let RW := regularization W
  have hRW := regularization_bijective W
  let Φ : Map (regularizeMap W).image (rvHeadStartBundle (regularizeMap A).image k (Fin.natAdd 1 ∘ lab)) :=
    H.map.comp (RW.inverse hRW)
  have hΦ : ∀ z : W, Φ (RW z) = H.map z := by
    intro z
    change H.map (RW.inverse hRW (RW z)) = _
    rw [Map.inverse_apply]
  have hfst : ∀ z : W, (H.map z).val.1 = z.val.1 :=
    carried_fst (regularization A) (regularization_bijective A) (fun _ => rfl) hL
  have htags : ∀ z : W, (H.map z).val.2 = (regularize (headStartBaseVF 1 k z.val.1, z.val.2)).2 := by
    intro z
    rw [H.labels z]
    change (regularize (headStartBaseProjection A k lab z).val).2 = _
    rw [headStartBaseProjection_value]
  have hextra : ∀ z : W, tupleRV M (headStartExtraVF 1 k z.val.1) = z.val.2 ∘ lab :=
    fun z => ((mem_rvHeadStartBundle A k lab z.val.1 z.val.2).mp z.property).2
  have hbij : Function.Bijective Φ := by
    refine H.bijective.comp ⟨fun a b h => ?_, fun x => ⟨RW x, by rw [Map.inverse_apply]⟩⟩
    obtain ⟨x, rfl⟩ := hRW.2 a
    obtain ⟨y, rfl⟩ := hRW.2 b
    rw [Map.inverse_apply, Map.inverse_apply] at h
    rw [h]
  symm
  change clsG hc (bundleGood g) = clsG hc (bundleGood (regHGood g))
  rw [← clsG_reg hc (bundleGood g)]
  refine clsG_eq_of_wholeFibres hc (regGood (bundleGood g)) (bundleGood (regHGood g)) Φ hbij ?_ ?_ ?_
  · apply wholeFibres_of_tags Φ hbij
    intro a b
    obtain ⟨z, rfl⟩ := hRW.2 a
    obtain ⟨w, rfl⟩ := hRW.2 b
    rw [hΦ, hΦ, htags, htags]
    change (regularize (headStartBaseVF 1 k z.val.1, z.val.2)).2 = (regularize (headStartBaseVF 1 k w.val.1, w.val.2)).2 ↔
      (regularize z.val).2 = (regularize w.val).2
    rw [regularize_snd_eq, regularize_snd_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      apply headStart_vf_ext k
      · change headStartBaseVF 1 k (rv M ∘ z.val.1) = headStartBaseVF 1 k (rv M ∘ w.val.1)
        rw [headStartBaseVF_comp, headStartBaseVF_comp]
        exact h1
      · change headStartExtraVF 1 k (rv M ∘ z.val.1) = headStartExtraVF 1 k (rv M ∘ w.val.1)
        rw [headStartExtraVF_comp, headStartExtraVF_comp]
        change tupleRV M (headStartExtraVF 1 k z.val.1) = tupleRV M (headStartExtraVF 1 k w.val.1)
        rw [hextra, hextra]
        simp only at h2
        rw [h2]
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      change rv M ∘ headStartBaseVF 1 k z.val.1 = rv M ∘ headStartBaseVF 1 k w.val.1
      rw [← headStartBaseVF_comp, ← headStartBaseVF_comp]
      exact congrArg (headStartBaseVF 1 k) h1
  · intro a
    obtain ⟨z, rfl⟩ := hRW.2 a
    rw [hΦ, hfst]
    rfl
  · intro a
    obtain ⟨z, rfl⟩ := hRW.2 a
    rw [hΦ]
    change (regHGood g).form (headStartBaseProjection _ k _ (H.map z)) = regForm (bundleGood g) (RW z)
    rw [regForm_apply, H.base z, regHGood_form]
    rfl

end Reg

/-! #### Zero-centred steps -/

section ZC
variable (h00 : M ⊨ Axioms.ACVF00)
variable {r : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)} {lab : Fin k → Fin r}

theorem mem_zcImage (g : HGood A lab) (Z : ZeroCenteredData A) {q : Mixed M 1 (1 + r)} :
    q ∈ Z.map.image.carrier ↔ ∃ p ∈ A.carrier, q = (p.1, Fin.append (fun _ : Fin 1 => branchTag (M := M) false) p.2) := by
  rw [ZeroCenteredData.image_carrier]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, zc_point Z g.vfBounded hp⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, zc_point Z g.vfBounded hp⟩

include h00 in
/-- The image of a zero-centred step of a head-start chain set. -/
def zcHGood (g : HGood A lab) (Z : ZeroCenteredData A) : HGood Z.map.image (Fin.natAdd 1 ∘ lab) where
  pullback := by
    show rvHull _ = _
    apply Set.Subset.antisymm
    · intro q hq
      obtain ⟨q', hq', h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
      obtain ⟨p, hp, rfl⟩ := (mem_zcImage g Z).mp hq'
      apply (mem_zcImage g Z).mpr
      refine ⟨(q.1, p.2), rvPullback_mem_of_sameRV g.pullback hp h1 rfl, ?_⟩
      exact Prod.ext rfl h2.symm
    · intro q hq
      exact (mem_rvHull_iff _ q).mpr ⟨q, hq, rfl, rfl⟩
  finite := by
    intro a t
    apply ((g.finite a t).image (fun u => Fin.append (fun _ : Fin 1 => branchTag (M := M) false) u)).subset
    rintro v ⟨hv, hl⟩
    obtain ⟨p, hp, he⟩ := (mem_zcImage g Z).mp hv
    have h1 : p.1 = a := (congrArg Prod.fst he).symm
    have h2 : v = Fin.append (fun _ : Fin 1 => branchTag (M := M) false) p.2 := congrArg Prod.snd he
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
    obtain ⟨p, hp, rfl⟩ := (mem_zcImage g Z).mp hq
    exact hγ p hp i
  rvBounded := by
    obtain ⟨δ, hδ⟩ := g.rvBounded
    have h1 : ((max δ 1)⁻¹).val ≤ (δ⁻¹).val := show (max δ 1)⁻¹ ≤ δ⁻¹ from inv_le_inv' (le_max_left _ _)
    have h2 : δ.val ≤ (max δ 1).val := show δ ≤ max δ 1 from le_max_left _ _
    have h3 : ((max δ 1)⁻¹).val ≤ (1 : Values.Gamma (M := M)).val :=
      show (max δ 1)⁻¹ ≤ 1 from inv_le_one'.mpr (le_max_right _ _)
    have h4 : (1 : Values.Gamma (M := M)).val ≤ (max δ 1).val := show 1 ≤ max δ 1 from le_max_right _ _
    refine ⟨max δ 1, fun q hq i => ?_⟩
    obtain ⟨p, hp, rfl⟩ := (mem_zcImage g Z).mp hq
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · change ((max δ 1)⁻¹).val ≤ Values.vrv (Fin.append (fun _ : Fin 1 => branchTag (M := M) false) p.2 (Fin.castAdd r i)) ∧
        Values.vrv (Fin.append (fun _ : Fin 1 => branchTag (M := M) false) p.2 (Fin.castAdd r i)) ≤ (max δ 1).val
      rw [Fin.append_left, branchTag_value]
      exact ⟨h3, h4⟩
    · change ((max δ 1)⁻¹).val ≤ Values.vrv (Fin.append (fun _ : Fin 1 => branchTag (M := M) false) p.2 (Fin.natAdd 1 i)) ∧
        Values.vrv (Fin.append (fun _ : Fin 1 => branchTag (M := M) false) p.2 (Fin.natAdd 1 i)) ≤ (max δ 1).val
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

theorem zcHGood_form (g : HGood A lab) (Z : ZeroCenteredData A) (p : A) :
    (zcHGood h00 g Z).form (Z.bijection p) = g.form p := by
  change g.form (Z.bijection.inverse _ (Z.bijection p)) = _
  rw [Map.inverse_apply]

include h00 in
/-- **A zero-centred step keeps the head-start class.** -/
theorem claimH_zc (Z : ZeroCenteredData A) : ClaimH hc k A Z.map.image Z.bijection := by
  intro lab g
  have hpt : ∀ p : A, (Z.bijection p).val = (p.val.1, Fin.append (fun _ : Fin 1 => branchTag (M := M) false) p.val.2) :=
    fun p => zc_point Z g.vfBounded p.property
  have hL : ∀ p : A, ∀ i, (Z.bijection p).val.2 ((Fin.natAdd 1 ∘ lab) i) = p.val.2 (lab i) := by
    intro p i
    rw [hpt]
    simp only [Function.comp_apply, Fin.append_right]
  refine ⟨Fin.natAdd 1 ∘ lab, hL, zcHGood h00 g Z, zcHGood_form h00 g Z, 0, ?_⟩
  rw [clsH_eq_of_retag hc g (zcHGood h00 g Z) Z.bijection (Z.bijective h00) ?_ (fun p => by rw [hpt]) hL
    (zcHGood_form h00 g Z)]
  · exact .refl _
  · apply wholeFibres_of_tags Z.bijection (Z.bijective h00)
    intro p q
    rw [hpt, hpt]
    exact ⟨fun h => append_ones_injective h, fun h => by simp only at h ⊢; rw [h]⟩

end ZC

/-- **A regularization step** for head-start chain sets. -/
theorem claimH_regularize {r : ℕ} (A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)) :
    ClaimH hc k A (regularizeMap A).image (regularization A) := by
  intro lab g
  refine ⟨Fin.natAdd 1 ∘ lab, fun p i => regularize_snd_right p.val (lab i), regHGood g, regHGood_form g, 0, ?_⟩
  rw [clsH_regHGood]
  exact .refl _

end Claims

/-! ### Relative steps and chains -/

section Rel
open DiamondIntegral.Section7.SpecialChains DiamondIntegral.Section7.SpecialChainRel
open DiamondIntegral.Section7.SpecialChainInduction
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.LiftClasses
open IntegrationInACVF.Section6.Iteration
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {k : ℕ}
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hsmall : Cardinal.mk (T : Set M) < κ)

theorem relPoint_tail {r : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
    (R : RelativeApertureData (G := G) A) (x : A) :
    (fun i => (R.bijection x).val.2 (Fin.natAdd 1 i)) = x.val.2 := by
  funext i
  rw [RelativeApertureData.bijection_apply]
  simp only [RelativeApertureData.point, Fin.append_right]

include h00 hκ hs hv hsmall in
/-- **A relative step on a head-start chain set is one blowup** (carried to
the head-start bundle, Section 7's `step_rel`). -/
theorem claimH_rel {r : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
    (R : RelativeApertureData (G := G) A) : ClaimH hc k A R.map.image R.bijection := by
  intro lab g
  let Rk := R.carryHeadStart h00 hc hκ hs hv k lab
  let Ig := imageGood hc (bundleGood g) Rk hκ hs hsmall h00
  have hE : Rk.map.image = rvHeadStartBundle R.map.image k (Fin.natAdd 1 ∘ lab) :=
    defSet_eq_of_carrier_eq (R.carryHeadStart_image h00 hc hκ hs hv k lab)
  let Ib := transport hE Ig
  have hL : ∀ p : A, ∀ i, (R.bijection p).val.2 ((Fin.natAdd 1 ∘ lab) i) = p.val.2 (lab i) := by
    intro p i
    exact congrFun (relPoint_tail R p) (lab i)
  let g' : HGood R.map.image (Fin.natAdd 1 ∘ lab) :=
    { pullback := unbundle_pullback Ib.pullback
      finite := unbundle_finite Ib.finite
      vfBounded := unbundle_vfBounded Ib.vfBounded
      rvBounded := unbundle_rvBounded Ib.rvBounded
      form := g.form.comp (R.bijection.inverse (R.bijective h00))
      form_labels := by
        intro p q he
        obtain ⟨a, rfl⟩ := (R.bijective h00).2 p
        obtain ⟨b, rfl⟩ := (R.bijective h00).2 q
        change g.form (R.bijection.inverse _ (R.bijection a)) = g.form (R.bijection.inverse _ (R.bijection b))
        rw [Map.inverse_apply, Map.inverse_apply]
        apply g.form_labels
        rw [← relPoint_tail R a, ← relPoint_tail R b, he] }
  have hform' : ∀ p : A, g'.form (R.bijection p) = g.form p := by
    intro p
    change g.form (R.bijection.inverse _ (R.bijection p)) = _
    rw [Map.inverse_apply]
  refine ⟨Fin.natAdd 1 ∘ lab, hL, g', hform', 1, ?_⟩
  have hstep := step_rel hc (bundleGood g) Rk hκ hs hsmall h00
  have hcls : clsG hc Ig = clsH hc g' := by
    apply clsG_congr hc hE Ig (bundleGood g')
    intro p
    obtain ⟨z, rfl⟩ := (Rk.bijective h00).2 p
    rw [imageGood_form]
    change g'.form (headStartBaseProjection R.map.image k (Fin.natAdd 1 ∘ lab) ⟨(Rk.bijection z).val, _⟩) =
      g.form (headStartBaseProjection A k lab z)
    have hproj : headStartBaseProjection R.map.image k (Fin.natAdd 1 ∘ lab) ⟨(Rk.bijection z).val, hE ▸ (Rk.bijection z).property⟩ =
        R.bijection (headStartBaseProjection A k lab z) := by
      apply Subtype.ext
      rw [headStartBaseProjection_value, RelativeApertureData.bijection_apply,
        RelativeApertureData.bijection_apply, headStartBaseProjection_value]
      exact R.carryHeadStart_point h00 hc hκ hs hv k lab z.val z.property
    rw [hproj, hform']
  exact Steps.single (hcls ▸ hstep)

include h00 hκ hs hv hsmall in
/-- A step given by relative data with the same point map. -/
theorem claimH_of_point {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)} (f : Map A B) (hs1 : s = 1 + r)
    (R : RelativeApertureData (G := G) A) (hB : B.carrier = hs1 ▸ R.map.image.carrier)
    (hf : ∀ p : A, (f p).val = hs1 ▸ R.point p.val) : ClaimH hc k A B f := by
  subst hs1
  have hE : R.map.image = B := DefSet.eq_of_carrier_eq hB.symm
  intro lab g
  obtain ⟨lab', hL, g', hform, m, hm⟩ := claimH_rel hc h00 hκ hs hv hsmall R lab g
  have hfp : ∀ p : A, f p = ⟨(R.bijection p).val, hE ▸ (R.bijection p).property⟩ := fun p => Subtype.ext (hf p)
  refine ⟨lab', fun p i => ?_, g'.transport hE, fun p => ?_, m, ?_⟩
  · rw [hfp p]
    exact hL p i
  · rw [hfp p, HGood.transport_form, hform]
  · rw [clsH_transport]
    exact hm

include h00 hκ hs hv hsmall in
/-- **The head-start Lemma 7.11 along special covariant chains.** -/
theorem claimH_special {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)} {f : Map A B}
    (h : SpecialCovariantChain (G := G) A B f) : ClaimH hc k A B f := by
  induction h with
  | identity A _ =>
    intro lab g
    exact ⟨lab, fun _ _ => rfl, g, fun _ => rfl, 0, .refl _⟩
  | regularize A _ _ => exact claimH_regularize hc A
  | centripetal A D =>
    exact claimH_of_point hc h00 hκ hs hv hsmall D.bijection rfl D.relativeData
      (by rw [RelativeApertureData.image_carrier, CentripetalData.image_carrier]
          ext q
          constructor
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, hp, D.relativeData_point ⟨p, hp⟩⟩
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, hp, (D.relativeData_point ⟨p, hp⟩).symm⟩)
      (fun p => (D.relativeData_point p).symm)
  | zeroCentered A D => exact claimH_zc hc h00 D
  | comp _ _ ihf ihg => exact claimH_comp hc ihf ihg

include h00 hκ hs hv hsmall in
/-- **The head-start Lemma 7.11 along relative aperture chains.** -/
theorem claimH_relative_chain {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
    {B : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)} {f : Map A B}
    (h : RelativeApertureChain (G := G) A B f) : ClaimH hc k A B f := by
  induction h with
  | original h => exact claimH_special hc h00 hκ hs hv hsmall h
  | relative A D => exact claimH_rel hc h00 hκ hs hv hsmall D
  | comp _ _ ihf ihg => exact claimH_comp hc ihf ihg

end Rel

end DiamondIntegral.Section7.Lemma714Head
