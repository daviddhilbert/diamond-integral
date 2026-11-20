import «section 7».Lemma714HeadSteps

/-! Lemma 7.11 (`special:to:blowup:coa`) for partial lifts, part 1: head-start
chain sets with `n` VF coordinates and their classes.

The proof of Lemma 7.14 (Comparison step) applies Lemma 7.11 to a *partial*
lift: an object `U ∈ μRV^db[n+k]` of which only `n` coordinates are lifted to
VF, the remaining `k` being kept as RV coordinates (a head start). The author
approved formalizing 7.11 in this form (`section 7/PLAN.md`, Question C).

A *head-start chain set* `HGoodN X λ` is a set `X ⊆ VF^n × RV^r` with labels
`λ : Fin k → Fin r` that is an RV pullback, VF and RV doubly bounded, whose
fibres over `(a, u ∘ λ)` are finite, together with a label-constant Γ-form.
Its head-start bundle (Section 6 `rvHeadStartBundle`, the `k` labels lifted to
VF coordinates) is a chain set of the full-lift Lemma 7.11 in grade `n + k`
(`bundleGoodN`), and the class of `X` is the class of the bundle (`clsHN`).
A bijection that keeps the VF coordinates, maps whole label fibres, keeps the
selected labels and transports the form does not change the class
(`clsHN_eq_of_retag`).

This generalizes `Lemma714Head.HGood` (one VF coordinate) to `n` coordinates;
for `n = 1` the two notions and their classes coincide (`HGoodN.ofH`,
`HGoodN.toH`, `clsHN_ofH`).

Blowups (`BlowupSteps`) are defined on classes of grade `1 + d`. A class of
grade `n + k` is compared through `gradeCast`, and `Reached x y` says that `y`
is reached from `x` by a blowup chain whenever the grade is written as `1 + d`
(`reached_iff`: for grade `1 + d` this is `∃ m, BlowupSteps m x y`). -/

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
open DiamondIntegral.Section7.SpecialChains DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.Lemma714Head DiamondIntegral.Section7.BlowupCongruence
open DiamondIntegral.Section7.ElementaryBlowups
open IntegrationInACVF.Section6.Iteration

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ### Blowup reachability in any grade -/

section Reach
open SpecialTransformations.Section3.GammaParameters
variable {B : Base (M := M)}

/-- A class of grade `N` read in grade `1 + d`, along `N = 1 + d`. -/
def gradeCast {N d : ℕ} (h : N = 1 + d) (x : Cls B N) : Cls B (1 + d) := h ▸ x

theorem gradeCast_rfl {d : ℕ} (x : Cls B (1 + d)) : gradeCast rfl x = x := rfl

/-- `y` is reached from `x` by a blowup chain (in the grade written as `1 + d`). -/
def Reached {N : ℕ} (x y : Cls B N) : Prop :=
  ∀ (d : ℕ) (h : N = 1 + d), ∃ m, BlowupSteps m (gradeCast h x) (gradeCast h y)

theorem reached_iff {d : ℕ} {x y : Cls B (1 + d)} : Reached x y ↔ ∃ m, BlowupSteps m x y := by
  constructor
  · intro h
    exact h d rfl
  · rintro ⟨m, hm⟩ d' h
    obtain rfl : d = d' := by omega
    exact ⟨m, hm⟩

theorem Reached.refl {N : ℕ} (x : Cls B N) : Reached x x := fun _ _ => ⟨0, .refl _⟩

theorem Reached.trans {N : ℕ} {x y z : Cls B N} (h1 : Reached x y) (h2 : Reached y z) : Reached x z := by
  intro d h
  obtain ⟨m1, s1⟩ := h1 d h
  obtain ⟨m2, s2⟩ := h2 d h
  exact ⟨m1 + m2, s1.trans s2⟩

theorem Reached.of_eq {N : ℕ} {x y : Cls B N} (h : x = y) : Reached x y := h ▸ Reached.refl x

theorem Reached.of_step {d : ℕ} {x y : Cls B (1 + d)} (h : Step x y) : Reached x y :=
  reached_iff.mpr ⟨1, Steps.single h⟩

end Reach

/-! ### Head-start chain sets with `n` VF coordinates -/

section HGoodDef
variable {T : LRV.Substructure M} {n r k : ℕ}

/-- A chain set with `n` VF coordinates and head-start labels `λ`. -/
structure HGoodN (X : DefSet (rawMixedSpace (M := M) n r) (T : Set M)) (lab : Fin k → Fin r) where
  pullback : IsRVPullback X.carrier
  finite : ∀ (a : Fin n → VF M) (t : Fin k → RVInfinity M),
    {u : Fin r → RVInfinity M | (a, u) ∈ X.carrier ∧ u ∘ lab = t}.Finite
  vfBounded : VFDoublyBounded X.carrier
  rvBounded : RVSupportDoublyBounded X.carrier
  form : Map X (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))
  form_labels : ∀ p q : X, p.val.2 = q.val.2 → form p = form q

variable {X : DefSet (rawMixedSpace (M := M) n r) (T : Set M)} {lab : Fin k → Fin r}

/-- The head-start bundle of a head-start chain set is a chain set of grade
`n + k`. -/
def bundleGoodN (g : HGoodN X lab) : Good T (rvHeadStartBundle X k lab) where
  pullback := rvHeadStartBundle_pullback X k lab g.pullback
  finite := rvHeadStartBundle_finite_rv_fibres X k lab g.finite
  vfBounded := rvHeadStartBundle_doublyBounded X k lab g.vfBounded g.rvBounded
  rvBounded := rvHeadStartBundle_rvBounded X k lab g.rvBounded
  form := g.form.comp (headStartBaseProjection X k lab)
  form_labels := fun p q he => g.form_labels _ _ (by
    rw [headStartBaseProjection_value, headStartBaseProjection_value]
    exact he)

theorem bundleGoodN_form (g : HGoodN X lab) (p : rvHeadStartBundle X k lab) :
    (bundleGoodN g).form p = g.form (headStartBaseProjection X k lab p) := rfl

variable (hc : CanonicalStructure.IsCanonical (M := M))

/-- **The class of a head-start chain set**, in grade `n + k`: the class of its
head-start bundle. -/
def clsHN (g : HGoodN X lab) : Cls (BT T) (n + k) := clsG hc (bundleGoodN g)

end HGoodDef

/-! ### One VF coordinate -/

section One
variable {T : LRV.Substructure M} {r k : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)} {lab : Fin k → Fin r}

/-- A unary head-start chain set (`Lemma714Head.HGood`) as a head-start chain
set with `n = 1`. -/
def HGoodN.ofH (g : HGood X lab) : HGoodN X lab :=
  ⟨g.pullback, g.finite, g.vfBounded, g.rvBounded, g.form, g.form_labels⟩

/-- A head-start chain set with `n = 1` as a unary head-start chain set. -/
def HGoodN.toH (g : HGoodN X lab) : HGood X lab :=
  ⟨g.pullback, g.finite, g.vfBounded, g.rvBounded, g.form, g.form_labels⟩

variable (hc : CanonicalStructure.IsCanonical (M := M))

theorem clsHN_ofH (g : HGood X lab) : clsHN hc (HGoodN.ofH g) = clsH hc g := rfl

theorem clsH_toH (g : HGoodN X lab) : clsH hc g.toH = clsHN hc g := rfl

end One

/-! ### Carried bijections and retagging -/

section Retag
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {n r s k : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) n r) (T : Set M)} {Y : DefSet (rawMixedSpace (M := M) n s) (T : Set M)}
  {lab : Fin k → Fin r} {lab' : Fin k → Fin s}

/-- A carried bijection of head-start bundles maps whole label fibres. -/
theorem carried_wholeFibresN (f : Map X Y) (hf : Function.Bijective f) (hm : MapsWholeTagFibres f)
    (hL : ∀ p : X, ∀ i, (f p).val.2 (lab' i) = p.val.2 (lab i)) :
    MapsWholeTagFibres (carryHeadStartBijection f hf k lab lab' hL).map := by
  let H := carryHeadStartBijection f hf k lab lab' hL
  intro p b
  constructor
  · intro hb
    rw [H.labels p] at hb
    have hbY : (headStartBaseVF n k b.val.1, b.val.2) ∈ Y.carrier :=
      ((mem_rvHeadStartBundle Y k lab' b.val.1 b.val.2).mp b.property).1
    obtain ⟨x, hx, hfx⟩ := (hm (headStartBaseProjection X k lab p) ⟨_, hbY⟩).mp hb
    have hxp : x.val.2 = p.val.2 := by
      rw [hx, headStartBaseProjection_value]
    have hextra : tupleRV M (headStartExtraVF n k b.val.1) = x.val.2 ∘ lab := by
      rw [((mem_rvHeadStartBundle Y k lab' b.val.1 b.val.2).mp b.property).2]
      funext i
      simp only [Function.comp_apply]
      rw [← hL x i, hfx]
    let a0 : Mixed M (n + k) r := (Fin.append x.val.1 (headStartExtraVF n k b.val.1), x.val.2)
    have ha0 : a0 ∈ (rvHeadStartBundle X k lab).carrier := by
      apply (mem_rvHeadStartBundle X k lab a0.1 a0.2).mpr
      simp only [a0, headStartBaseVF_append, headStartExtraVF_append]
      exact ⟨x.property, hextra⟩
    refine ⟨⟨a0, ha0⟩, hxp, ?_⟩
    have hproj : headStartBaseProjection X k lab ⟨a0, ha0⟩ = x := by
      apply Subtype.ext
      rw [headStartBaseProjection_value]
      simp only [a0, headStartBaseVF_append, Prod.mk.eta]
    apply Subtype.ext
    have hbase := congrArg Subtype.val (H.base ⟨a0, ha0⟩)
    rw [hproj, hfx, headStartBaseProjection_value] at hbase
    have hfix := H.fixed ⟨a0, ha0⟩
    have h1 : headStartBaseVF n k (H.map ⟨a0, ha0⟩).val.1 = headStartBaseVF n k b.val.1 :=
      congrArg (fun z : Mixed M n s => z.1) hbase
    have h2 : (H.map ⟨a0, ha0⟩).val.2 = b.val.2 := congrArg (fun z : Mixed M n s => z.2) hbase
    have h3 : headStartExtraVF n k (H.map ⟨a0, ha0⟩).val.1 = headStartExtraVF n k b.val.1 := by
      rw [hfix]
      simp only [a0, headStartExtraVF_append]
    exact (Prod.ext (headStart_vf_ext k _ _ h1 h3) h2 : ((H.map ⟨a0, ha0⟩).val : Mixed M (n + k) s) = b.val)
  · rintro ⟨a, ha, rfl⟩
    rw [H.labels a, H.labels p]
    apply MapsWholeTagFibres.labels f hm
    rw [headStartBaseProjection_value, headStartBaseProjection_value]
    exact ha

/-- The VF part is kept by a carried map of a VF-preserving map. -/
theorem carried_fstN (f : Map X Y) (hf : Function.Bijective f) (hvf : ∀ p : X, (f p).val.1 = p.val.1)
    (hL : ∀ p : X, ∀ i, (f p).val.2 (lab' i) = p.val.2 (lab i)) (p : rvHeadStartBundle X k lab) :
    ((carryHeadStartBijection f hf k lab lab' hL).map p).val.1 = p.val.1 := by
  let H := carryHeadStartBijection f hf k lab lab' hL
  apply headStart_vf_ext k
  · have hbase := congrArg Subtype.val (H.base p)
    rw [headStartBaseProjection_value] at hbase
    have h1 : headStartBaseVF n k (H.map p).val.1 = (f (headStartBaseProjection X k lab p)).val.1 :=
      congrArg (fun z : Mixed M n s => z.1) hbase
    rw [h1, hvf, headStartBaseProjection_value]
  · exact H.fixed p

/-- **Retagging keeps the head-start class.** -/
theorem clsHN_eq_of_retag (g : HGoodN X lab) (g' : HGoodN Y lab') (f : Map X Y) (hf : Function.Bijective f)
    (hm : MapsWholeTagFibres f) (hvf : ∀ p : X, (f p).val.1 = p.val.1)
    (hL : ∀ p : X, ∀ i, (f p).val.2 (lab' i) = p.val.2 (lab i)) (hform : ∀ p : X, g'.form (f p) = g.form p) :
    clsHN hc g = clsHN hc g' := by
  let H := carryHeadStartBijection f hf k lab lab' hL
  exact clsG_eq_of_wholeFibres hc (bundleGoodN g) (bundleGoodN g') H.map H.bijective
    (carried_wholeFibresN f hf hm hL) (carried_fstN f hf hvf hL)
    (fun p => by
      change g'.form (headStartBaseProjection Y k lab' (H.map p)) = g.form (headStartBaseProjection X k lab p)
      rw [H.base p, hform])

end Retag

end DiamondIntegral.Section7.Lemma711Partial
