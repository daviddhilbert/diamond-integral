import «section 7».Lemma714HeadCarry
import «section 7».SpecialChainInduction

/-! Lemma 7.14, part 14: head-start chain sets and their classes.

For the head-start form of Lemma 7.13, a *head-start chain set* (`HGood`) is a
unary tagged RV-pullback `X ⊆ VF × RV^r` with labels `λ : Fin k → Fin r` such
that the fibres over `(a, u ∘ λ)` are finite, together with a label-constant
Γ-form. Its RV fibres over a VF point may be infinite. Its head-start bundle
(Section 6 `rvHeadStartBundle`, the labels lifted to VF coordinates) is a
chain set of Lemma 7.11 in grade `1 + k` (`bundleGood`), and the class of `X`
is the class of the bundle (`clsH`). By `clsH_eq_hsObj` it is the class of the
contraction of the bundle, i.e. of the head-start object.

A bijection that keeps the VF coordinate, maps whole label fibres, keeps the
selected labels and transports the form does not change the class
(`clsH_eq_of_retag`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma714Head
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.SpecialChains DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.ChartOfMeasured

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ### Base and extra coordinates of head-start tuples -/

section Tuples
variable {X : Type*} {n : ℕ}

omit [LRV.Structure M] hM in
theorem headStart_vf_ext : ∀ (k : ℕ) (z w : Fin (n + k) → X),
    headStartBaseVF n k z = headStartBaseVF n k w → headStartExtraVF n k z = headStartExtraVF n k w → z = w
  | 0, z, w, hb, _ => hb
  | k + 1, z, w, hb, he => by
    have hlast : z (Fin.last (n + k)) = w (Fin.last (n + k)) := by
      have := congrFun he (Fin.last k)
      simpa only [headStartExtraVF, Fin.lastCases_last] using this
    have hinit : Fin.init z = Fin.init w := by
      apply headStart_vf_ext k (Fin.init z) (Fin.init w) hb
      funext j
      have := congrFun he j.castSucc
      simpa only [headStartExtraVF, Fin.lastCases_castSucc] using this
    rw [← Fin.snoc_init_self z, ← Fin.snoc_init_self w, hinit]
    exact congrArg _ hlast

omit [LRV.Structure M] hM in
theorem init_append_succ {k : ℕ} (x : Fin n → X) (e : Fin (k + 1) → X) :
    Fin.init (Fin.append x e : Fin (n + (k + 1)) → X) = Fin.append x (Fin.init e) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · simp only [Fin.init]
    have h1 : (Fin.castSucc (Fin.castAdd k l) : Fin (n + (k + 1))) = Fin.castAdd (k + 1) l := Fin.ext rfl
    rw [h1, Fin.append_left, Fin.append_left]
  · simp only [Fin.init]
    have h1 : (Fin.castSucc (Fin.natAdd n l) : Fin (n + (k + 1))) = Fin.natAdd n l.castSucc := Fin.ext rfl
    rw [h1, Fin.append_right, Fin.append_right]
    rfl

omit [LRV.Structure M] hM in
theorem last_append_succ {k : ℕ} (x : Fin n → X) (e : Fin (k + 1) → X) :
    (Fin.append x e : Fin (n + (k + 1)) → X) (Fin.last (n + k)) = e (Fin.last k) := by
  have h1 : (Fin.last (n + k) : Fin (n + (k + 1))) = Fin.natAdd n (Fin.last k) := Fin.ext rfl
  rw [h1, Fin.append_right]

omit [LRV.Structure M] hM in
theorem headStartBaseVF_append : ∀ (k : ℕ) (x : Fin n → X) (e : Fin k → X),
    headStartBaseVF n k (Fin.append x e) = x
  | 0, x, e => by
    funext i
    exact Fin.append_left x e i
  | k + 1, x, e => by
    change headStartBaseVF n k (Fin.init (Fin.append x e : Fin (n + (k + 1)) → X)) = x
    rw [init_append_succ]
    exact headStartBaseVF_append k x (Fin.init e)

omit [LRV.Structure M] hM in
theorem headStartExtraVF_append : ∀ (k : ℕ) (x : Fin n → X) (e : Fin k → X),
    headStartExtraVF n k (Fin.append x e) = e
  | 0, x, e => Subsingleton.elim _ _
  | k + 1, x, e => by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [headStartExtraVF, Fin.lastCases_last]
      exact last_append_succ x e
    · simp only [headStartExtraVF, Fin.lastCases_castSucc]
      rw [init_append_succ, headStartExtraVF_append k x (Fin.init e)]
      rfl

end Tuples

/-! ### Head-start chain sets -/

section HGoodDef
variable {T : LRV.Substructure M} {r k : ℕ}

/-- A unary chain set with head-start labels `λ`. -/
structure HGood (X : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)) (lab : Fin k → Fin r) where
  pullback : IsRVPullback X.carrier
  tagged : ∀ p ∈ X.carrier, ∀ q ∈ X.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1
  finite : ∀ (a : Fin 1 → VF M) (t : Fin k → RVInfinity M),
    {u : Fin r → RVInfinity M | (a, u) ∈ X.carrier ∧ u ∘ lab = t}.Finite
  vfBounded : VFDoublyBounded X.carrier
  rvBounded : RVSupportDoublyBounded X.carrier
  form : Map X (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))
  form_labels : ∀ p q : X, p.val.2 = q.val.2 → form p = form q

variable {X : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)} {lab : Fin k → Fin r}

/-- The head-start bundle of a head-start chain set is a chain set of grade
`1 + k`. -/
def bundleGood (g : HGood X lab) : Good T (rvHeadStartBundle X k lab) where
  pullback := rvHeadStartBundle_pullback X k lab g.pullback
  finite := rvHeadStartBundle_finite_rv_fibres X k lab g.finite
  vfBounded := rvHeadStartBundle_doublyBounded X k lab g.vfBounded g.rvBounded
  rvBounded := rvHeadStartBundle_rvBounded X k lab g.rvBounded
  form := g.form.comp (headStartBaseProjection X k lab)
  form_labels := fun p q he => g.form_labels _ _ (by
    rw [headStartBaseProjection_value, headStartBaseProjection_value]
    exact he)

theorem bundleGood_form (g : HGood X lab) (p : rvHeadStartBundle X k lab) :
    (bundleGood g).form p = g.form (headStartBaseProjection X k lab p) := rfl

variable (hc : CanonicalStructure.IsCanonical (M := M))

/-- **The class of a head-start chain set**, in grade `1 + k`. -/
def clsH (g : HGood X lab) : Cls (BT T) (1 + k) := clsG hc (bundleGood g)

/-- The head-start object of `X`: the contraction of the bundle. -/
def hsObj (g : HGood X lab) : MeasuredRVObject (M := M) (T : Set M) (1 + k) :=
  contractedMeasuredRVObject (rvHeadStartBundle X k lab) (rvHeadStartBundle_tagged X k lab g.tagged)
    (bundleGood g).pullback (bundleGood g).finite (bundleGood g).vfBounded (bundleGood g).form
    (bundleGood g).form_labels

theorem hsObj_db (g : HGood X lab) : (hsObj g).doublyBounded :=
  contractedMeasuredRVObject_doublyBounded _ _ _ _ _ (bundleGood g).rvBounded _ _

end HGoodDef

/-- The class of a tagged chain set is the class of its (unregularized)
contraction. -/
theorem clsG_eq_contr (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {n r : ℕ}
    {X : DefSet (rawMixedSpace (M := M) n r) (T : Set M)} (g : Good T X)
    (hT : ∀ p ∈ X.carrier, ∀ q ∈ X.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    clsG hc g = cls (objOf hc T (contractedMeasuredRVObject X hT g.pullback g.finite g.vfBounded g.form g.form_labels)
      (contractedMeasuredRVObject_doublyBounded _ _ _ _ _ g.rvBounded _ _)) := by
  unfold clsG
  apply cls_objOf_eq hc
  exact (contractionIso hT g.pullback g.finite g.vfBounded g.form g.form_labels
    (regularize_tagged X) (regularize_pullback X g.pullback) (regularize_finite X g.finite)
    (regularize_vfDoublyBounded X g.vfBounded) (regForm g) (regForm_labels g)
    (regularization X) (regularization_bijective X) (regularization_matching X hT) (fun _ => rfl)
    (fun p => regForm_apply g p)).symm

section Retag
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {r s k : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)} {Y : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)}
  {lab : Fin k → Fin r} {lab' : Fin k → Fin s}

theorem clsH_eq_hsObj (g : HGood X lab) : clsH hc g = cls (objOf hc T (hsObj g) (hsObj_db g)) :=
  clsG_eq_contr hc (bundleGood g) _

/-- A carried bijection of head-start bundles maps whole label fibres. -/
theorem carried_wholeFibres (f : Map X Y) (hf : Function.Bijective f) (hm : MapsWholeTagFibres f)
    (hL : ∀ p : X, ∀ i, (f p).val.2 (lab' i) = p.val.2 (lab i)) :
    MapsWholeTagFibres (carryHeadStartBijection f hf k lab lab' hL).map := by
  let H := carryHeadStartBijection f hf k lab lab' hL
  intro p b
  constructor
  · intro hb
    rw [H.labels p] at hb
    have hbY : (headStartBaseVF 1 k b.val.1, b.val.2) ∈ Y.carrier :=
      ((mem_rvHeadStartBundle Y k lab' b.val.1 b.val.2).mp b.property).1
    obtain ⟨x, hx, hfx⟩ := (hm (headStartBaseProjection X k lab p) ⟨_, hbY⟩).mp hb
    have hxp : x.val.2 = p.val.2 := by
      rw [hx, headStartBaseProjection_value]
    have hextra : tupleRV M (headStartExtraVF 1 k b.val.1) = x.val.2 ∘ lab := by
      rw [((mem_rvHeadStartBundle Y k lab' b.val.1 b.val.2).mp b.property).2]
      funext i
      simp only [Function.comp_apply]
      rw [← hL x i, hfx]
    let a0 : Mixed M (1 + k) r := (Fin.append x.val.1 (headStartExtraVF 1 k b.val.1), x.val.2)
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
    have h1 : headStartBaseVF 1 k (H.map ⟨a0, ha0⟩).val.1 = headStartBaseVF 1 k b.val.1 :=
      congrArg (fun z : Mixed M 1 s => z.1) hbase
    have h2 : (H.map ⟨a0, ha0⟩).val.2 = b.val.2 := congrArg (fun z : Mixed M 1 s => z.2) hbase
    have h3 : headStartExtraVF 1 k (H.map ⟨a0, ha0⟩).val.1 = headStartExtraVF 1 k b.val.1 := by
      rw [hfix]
      simp only [a0, headStartExtraVF_append]
    exact (Prod.ext (headStart_vf_ext k _ _ h1 h3) h2 : ((H.map ⟨a0, ha0⟩).val : Mixed M (1 + k) s) = b.val)
  · rintro ⟨a, ha, rfl⟩
    rw [H.labels a, H.labels p]
    apply MapsWholeTagFibres.labels f hm
    rw [headStartBaseProjection_value, headStartBaseProjection_value]
    exact ha

/-- **Retagging keeps the head-start class.** -/
theorem clsH_eq_of_retag (g : HGood X lab) (g' : HGood Y lab') (f : Map X Y) (hf : Function.Bijective f)
    (hm : MapsWholeTagFibres f) (hvf : ∀ p : X, (f p).val.1 = p.val.1)
    (hL : ∀ p : X, ∀ i, (f p).val.2 (lab' i) = p.val.2 (lab i)) (hform : ∀ p : X, g'.form (f p) = g.form p) :
    clsH hc g = clsH hc g' := by
  rw [clsH_eq_hsObj, clsH_eq_hsObj]
  apply cls_objOf_eq hc
  let H := carryHeadStartBijection f hf k lab lab' hL
  have hfst : ∀ p : rvHeadStartBundle X k lab, (H.map p).val.1 = p.val.1 := by
    intro p
    apply headStart_vf_ext k
    · have hbase := congrArg Subtype.val (H.base p)
      rw [headStartBaseProjection_value] at hbase
      have h1 : headStartBaseVF 1 k (H.map p).val.1 = (f (headStartBaseProjection X k lab p)).val.1 :=
        congrArg (fun z : Mixed M 1 s => z.1) hbase
      rw [h1, hvf, headStartBaseProjection_value]
    · exact H.fixed p
  exact contractionIso _ _ _ _ _ _ _ _ _ _ _ _ H.map H.bijective (carried_wholeFibres f hf hm hL)
    (fun p => by rw [hfst p])
    (fun p => by
      change g'.form (headStartBaseProjection Y k lab' (H.map p)) = g.form (headStartBaseProjection X k lab p)
      rw [H.base p, hform])

end Retag

end DiamondIntegral.Section7.Lemma714Head
