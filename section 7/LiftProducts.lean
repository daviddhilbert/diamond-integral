import «section 7».LiftClasses
import «section 6».DiamondProduct
import «section 6».DiamondGroupoidMaps

/-! The lift of a product chart is the product of the lifts (for the ring
structure of `μ𝕃 : K μRV^db[*] → K μVF^◇[*]`, Theorem 7.26 and Corollary 6.37).

For bounded charts `a` (degree `k`) and `b` (degree `l`), Section 4's product
`a × b` has degree `l + k`, arity `arity b + arity a` and coordinates
`join l k (a-coordinates) (b-coordinates)`, while Section 6's product of
objects of `μVF^◇` has degree `k + l` and uses `Fin.append`. In value order
both put the `a`-block first. The strict (`∞`-free) form of a chart doubles
the labels into a value block and a tag block, so the labels of
`strict (a × b)` come in the order `y_a, y_b, t_a, t_b` and those of
`strict a × strict b` in the order `y_a, t_a, y_b, t_b`.

* `relabel_isomorphic`: two objects of `μVF^◇[n]` whose carriers and forms
  correspond under a label bijection `e` are isomorphic, by
  `(x, t) ↦ (x, t ∘ e)` (a VF-fixing, hence relatively unary, proper
  covariant homeomorphism with unit Jacobian). `relabel_isomorphic_cast`
  allows a degree cast `h ▸ B`, reading VF coordinates through `Fin.cast h`.
* `prodLabel`: the label bijection between `strict a × strict b` and
  `strict (a × b)`, with `encode_prodLabel`.
* `lift_product_isomorphic`: the lift of `a × b` is isomorphic to
  `Nat.add_comm k l ▸ (lift a × lift b)`; `lift_product_sigma` is the same
  statement for graded elements `Σ n, μVF^◇[n]`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.LiftProducts
open DiamondIntegral.Section2 DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGroupoid

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-! ### Relabelling isomorphisms -/

section Relabel
variable {S : Set M} {n m r s : ℕ}

/-- Reading the VF coordinates through `c` and the labels through `e`. -/
def relabelPoint (c : Fin n → Fin m) (e : Fin s → Fin r) (p : Mixed M m r) : Mixed M n s :=
  (p.1 ∘ c, p.2 ∘ e)

/-- The definable map `(x, t) ↦ (x ∘ c, t ∘ e)`. -/
def relabelMap (A : DefSet (rawMixedSpace (M := M) m r) S) (c : Fin n → Fin m) (e : Fin s → Fin r) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n s) S) := by
  let P := rawMixedSpace (M := M) m r
  let codes (z : Fin m ⊕ Fin r → M) : Fin n ⊕ Fin s → M :=
    Sum.elim (fun i => z (.inl (c i))) (fun j => z (.inr (e j)))
  have hcodes : S.DefinableMap LRV codes := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hcode (z : P.domain) : mixedValues (relabelPoint c e (P.decode z)) = codes z.val := by
    have he := mixedValues_decode z
    funext i
    cases i with
    | inl i => exact congrFun he (.inl (c i))
    | inr i => exact congrFun he (.inr (e i))
  have hdom (z : P.domain) : codes z.val ∈ (rawMixedSpace (M := M) n s).domain := by
    rw [← hcode z]
    exact mixedValues_mem_domain _
  exact Map.ofCodes A (relabelPoint c e) codes hcodes hdom
    (fun z => mixedValues_injective ((mixedValues_decode ⟨_, hdom z⟩).trans (hcode z).symm))

omit [M ⊨ Axioms.ACVF] in
theorem relabelMap_val (A : DefSet (rawMixedSpace (M := M) m r) S) (c : Fin n → Fin m)
    (e : Fin s → Fin r) (p : A) : (relabelMap A c e p).val = (p.val.1 ∘ c, p.val.2 ∘ e) := rfl

end Relabel

/-! ### Relabelling isomorphisms of `μVF^◇[n]` -/

section Iso
variable {S : Set M} {n : ℕ}

/-- The relabelling map between two objects: identity on VF coordinates. -/
def relabelHom (A B : VFObject (M := M) S n) (e : Fin B.labels → Fin A.labels)
    (hmem : ∀ p ∈ A.carrier.carrier, (p.1, p.2 ∘ e) ∈ B.carrier.carrier) : Map A.carrier B.carrier :=
  (relabelMap A.carrier id e).corestrict (fun p => hmem p.val p.property)

theorem relabelHom_val (A B : VFObject (M := M) S n) (e : Fin B.labels → Fin A.labels)
    (hmem : ∀ p ∈ A.carrier.carrier, (p.1, p.2 ∘ e) ∈ B.carrier.carrier) (p : A.carrier) :
    (relabelHom A B e hmem p).val = (p.val.1, p.val.2 ∘ e) := rfl

theorem relabel_source_iff (A B : VFObject (M := M) S n) (e : Fin B.labels → Fin A.labels)
    (hmem : ∀ p ∈ A.carrier.carrier, (p.1, p.2 ∘ e) ∈ B.carrier.carrier)
    (u : Fin A.labels → RVInfinity M) (v : Fin B.labels → RVInfinity M) (a : Fin n → VF M) :
    a ∈ graphFibreSource (relabelHom A B e hmem) u v ↔ (a, u) ∈ A.carrier.carrier ∧ u ∘ e = v := by
  constructor
  · rintro ⟨b, p, hp, hfp⟩
    refine ⟨hp ▸ p.property, ?_⟩
    have h2 := congrArg Prod.snd hfp
    have h1 := congrArg Prod.snd hp
    change p.val.2 ∘ e = v at h2
    change p.val.2 = u at h1
    rw [← h1]
    exact h2
  · rintro ⟨ha, rfl⟩
    exact ⟨a, ⟨(a, u), ha⟩, rfl, rfl⟩

theorem relabel_range_eq_source (A B : VFObject (M := M) S n) (e : Fin B.labels → Fin A.labels)
    (hmem : ∀ p ∈ A.carrier.carrier, (p.1, p.2 ∘ e) ∈ B.carrier.carrier)
    (u : Fin A.labels → RVInfinity M) (v : Fin B.labels → RVInfinity M) :
    graphFibreRange (relabelHom A B e hmem) u v = graphFibreSource (relabelHom A B e hmem) u v := by
  ext a
  constructor
  · rintro ⟨b, p, hp, hfp⟩
    have he : b = a := (congrArg Prod.fst hp).symm.trans (congrArg Prod.fst hfp)
    subst b
    exact ⟨a, p, hp, hfp⟩
  · rintro ⟨b, p, hp, hfp⟩
    have he : b = a := (congrArg Prod.fst hfp).symm.trans (congrArg Prod.fst hp)
    subst b
    exact ⟨a, p, hp, hfp⟩

/-- A relabelling fixes every VF coordinate. -/
theorem relabel_relativelyUnary (A B : VFObject (M := M) S n) (e : Fin B.labels → Fin A.labels)
    (hmem : ∀ p ∈ A.carrier.carrier, (p.1, p.2 ∘ e) ∈ B.carrier.carrier) (i : Fin n) :
    VFRelativelyUnary (relabelHom A B e hmem) i i := by
  intro p k _
  simp only [Equiv.symm_apply_apply]
  rfl

theorem relabel_continuous (A B : VFObject (M := M) S n) (e : Fin B.labels → Fin A.labels)
    (hmem : ∀ p ∈ A.carrier.carrier, (p.1, p.2 ∘ e) ∈ B.carrier.carrier) :
    ContinuousOnGraphFibres (G := G) (relabelHom A B e hmem) := by
  intro u v
  apply continuous_id.continuousOn.congr
  intro a ha
  obtain ⟨p, hp, hfp⟩ := graphFibreMap_graph (relabelHom A B e hmem) u v ha
  exact (congrArg Prod.fst hfp).symm.trans (congrArg Prod.fst hp)

theorem relabel_source_clopen (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A B : VFObject (M := M) S n) (e : Fin B.labels → Fin A.labels)
    (hmem : ∀ p ∈ A.carrier.carrier, (p.1, p.2 ∘ e) ∈ B.carrier.carrier)
    (u : Fin A.labels → RVInfinity M) (v : Fin B.labels → RVInfinity M) :
    IsClopen (graphFibreSource (relabelHom A B e hmem) u v) := by
  by_cases he : u ∘ e = v
  · have heq : graphFibreSource (relabelHom A B e hmem) u v = vfFibre A.carrier.carrier u := by
      ext a
      exact (relabel_source_iff A B e hmem u v a).trans (and_iff_left he)
    rw [heq]
    exact A.proper.clopen_fibres hv u
  · have heq : graphFibreSource (relabelHom A B e hmem) u v = ∅ := by
      ext a
      exact ⟨fun ha => False.elim (he ((relabel_source_iff A B e hmem u v a).mp ha).2), False.elim⟩
    rw [heq]
    exact isClopen_empty

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  (linear : GammaPiecewiseRationalAffineInput (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))

include h00 hc linear hκ hs hv hsmall hΓ in
/-- **Relabellings are isomorphisms.** If the labels of `A` and `B` correspond
under a bijection `e` that carries the carrier of `A` onto that of `B` and the
form of `A` to that of `B`, then `A` and `B` are isomorphic in `μVF^◇[n]`. The
isomorphism is `(x, t) ↦ (x, t ∘ e)`. -/
theorem relabel_isomorphic (A B : VFObject (M := M) S n) (e : Fin B.labels ≃ Fin A.labels)
    (hmem : ∀ (x : Fin n → VF M) (t : Fin A.labels → RVInfinity M),
      (x, t) ∈ A.carrier.carrier ↔ (x, t ∘ e) ∈ B.carrier.carrier)
    (hform : ∀ (x : Fin n → VF M) (t : Fin A.labels → RVInfinity M)
      (hA : (x, t) ∈ A.carrier.carrier) (hB : (x, t ∘ e) ∈ B.carrier.carrier),
      gammaMapValue A.form ⟨(x, t), hA⟩ = gammaMapValue B.form ⟨(x, t ∘ e), hB⟩) :
    Isomorphic G A B := by
  have hmemB : ∀ p ∈ A.carrier.carrier, (p.1, p.2 ∘ e) ∈ B.carrier.carrier :=
    fun p hp => (hmem p.1 p.2).mp hp
  let f : Map A.carrier B.carrier := relabelHom A B e hmemB
  have hf_val (p : A.carrier) : (f p).val = (p.val.1, p.val.2 ∘ e) := rfl
  have hbij : Function.Bijective f := by
    constructor
    · intro p q hpq
      have h := congrArg Subtype.val hpq
      rw [hf_val, hf_val] at h
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact (Prod.mk.inj h).1
      funext i
      have := congrFun (Prod.mk.inj h).2 (e.symm i)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using this
    · intro q
      have hq : (q.val.1, q.val.2 ∘ e.symm) ∈ A.carrier.carrier := by
        apply (hmem _ _).mpr
        have he : (q.val.2 ∘ e.symm) ∘ e = q.val.2 := by
          funext i
          simp only [Function.comp_apply, Equiv.symm_apply_apply]
        rw [he]
        exact q.property
      refine ⟨⟨_, hq⟩, Subtype.ext ?_⟩
      rw [hf_val]
      refine Prod.ext rfl ?_
      funext i
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have hcont : ContinuousOnGraphFibres (G := G) f := relabel_continuous A B e hmemB
  have hcov : ProperCovariant f :=
    properCovariant_of_clopen_ranges h00 hc hκ hs hv f A.proper B.proper hcont
      (fun u v => (relabel_source_clopen hv A B e hmemB u v).isOpen)
      (fun u v => (relabel_range_eq_source A B e hmemB u v).symm ▸ relabel_source_clopen hv A B e hmemB u v)
  have homeo : ProperCovariantHomeomorphism (G := G) f :=
    properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ f hcov hbij hcont
  have hunary : n = 0 ∨ ∃ i j : Fin n, VFRelativelyUnary f i j := by
    by_cases hn : n = 0
    · exact Or.inl hn
    · exact Or.inr ⟨⟨0, Nat.pos_of_ne_zero hn⟩, _, relabel_relativelyUnary A B e hmemB _⟩
  obtain ⟨K, _⟩ := morphism_of_generic_map h00 hc hs hsmall f hbij
    (UnaryFactorization.step homeo hunary) (fun p _ => by
      have hchart : IsVFChartAt f p id := by
        obtain ⟨ρ, hρ⟩ := identity_vfChart A.proper p
        refine ⟨ρ, fun x hx => ?_⟩
        obtain ⟨hxA, _⟩ := hρ x hx
        exact ⟨hxA, rfl⟩
      obtain ⟨L, hL, hdet⟩ := hasUnitJacobianAt_id p.val.1
      refine ⟨L, ⟨id, hchart, (hasDerivativeAt_iff_companion _ _ _).mp hL⟩, ?_⟩
      rw [hdet]
      have hfp : gammaMapValue A.form p = gammaMapValue B.form (f p) :=
        hform p.val.1 p.val.2 p.property (f p).property
      change vfValue 1 = (gammaMapValue A.form p / gammaMapValue B.form (f p)).val
      rw [hfp, div_self']
      change Values.vfValueHom 1 = Values.gammaValHom 1
      rw [map_one, map_one])
  exact ⟨K⟩

include h00 hc linear hκ hs hv hsmall hΓ in
/-- **Relabellings across a degree cast.** The same with the VF coordinates
read through `Fin.cast h`; the target is `h ▸ B`. -/
theorem relabel_isomorphic_cast {m : ℕ} (h : m = n) (A : VFObject (M := M) S n)
    (B : VFObject (M := M) S m) (e : Fin B.labels ≃ Fin A.labels)
    (hmem : ∀ (x : Fin n → VF M) (t : Fin A.labels → RVInfinity M),
      (x, t) ∈ A.carrier.carrier ↔ (x ∘ Fin.cast h, t ∘ e) ∈ B.carrier.carrier)
    (hform : ∀ (x : Fin n → VF M) (t : Fin A.labels → RVInfinity M)
      (hA : (x, t) ∈ A.carrier.carrier) (hB : (x ∘ Fin.cast h, t ∘ e) ∈ B.carrier.carrier),
      gammaMapValue A.form ⟨(x, t), hA⟩ = gammaMapValue B.form ⟨(x ∘ Fin.cast h, t ∘ e), hB⟩) :
    Isomorphic G A (h ▸ B) := by
  subst h
  exact relabel_isomorphic h00 hc linear hκ hs hv hsmall hΓ A B e hmem hform

end Iso

/-! ### Block indices -/

section Blocks
open DiamondIntegral.Section4.FiniteTupleBlocks DiamondIntegral.Section7.StrictCharts

theorem headIndex_val (n : ℕ) : (m : ℕ) → (i : Fin m) → (headIndex n m i).val = i.val
  | 0, i => i.elim0
  | m + 1, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [headIndex, Fin.cases_succ, Fin.val_succ, headIndex_val n m j]

theorem tailIndex_val (n : ℕ) : (m : ℕ) → (i : Fin n) → (tailIndex n m i).val = i.val + m
  | 0, i => rfl
  | m + 1, i => by
    simp only [tailIndex, Fin.val_succ, tailIndex_val n m i]
    omega

/-- In value order the first block of `Fin (k + l)` is the head block of
`Fin (l + k)`. -/
theorem cast_castAdd {k l : ℕ} (h : k + l = l + k) (i : Fin k) :
    Fin.cast h (Fin.castAdd l i) = headIndex l k i :=
  Fin.ext (by simp [headIndex_val])

/-- In value order the second block of `Fin (k + l)` is the tail block of
`Fin (l + k)`. -/
theorem cast_natAdd {k l : ℕ} (h : k + l = l + k) (j : Fin l) :
    Fin.cast h (Fin.natAdd k j) = tailIndex l k j :=
  Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd, tailIndex_val]; omega)

omit [LRV.Structure M] in
theorem join_comp_head {α : Type*} (n m : ℕ) (u : Fin m → α) (y : Fin n → α) :
    join n m u y ∘ headIndex n m = u := funext (join_head n m u y)

omit [LRV.Structure M] in
theorem join_comp_tail {α : Type*} (n m : ℕ) (u : Fin m → α) (y : Fin n → α) :
    join n m u y ∘ tailIndex n m = y := funext (join_tail n m u y)

/-- The labels of `strict a × strict b` (blocks `y_a, t_a, y_b, t_b`) read in
`strict (a × b)` (blocks `y_a, y_b, t_a, t_b`), with `p = arity a`,
`q = arity b`. -/
def prodLabelFun (p q : ℕ) : Fin ((p + p) + (q + q)) → Fin ((q + p) + (q + p)) :=
  Fin.append (join p p (fun i => headIndex (q + p) (q + p) (headIndex q p i))
      (fun i => tailIndex (q + p) (q + p) (headIndex q p i)))
    (join q q (fun j => headIndex (q + p) (q + p) (tailIndex q p j))
      (fun j => tailIndex (q + p) (q + p) (tailIndex q p j)))

/-- The inverse reading. -/
def prodLabelInv (p q : ℕ) : Fin ((q + p) + (q + p)) → Fin ((p + p) + (q + q)) :=
  join (q + p) (q + p)
    (join q p (fun i => Fin.castAdd (q + q) (headIndex p p i))
      (fun j => Fin.natAdd (p + p) (headIndex q q j)))
    (join q p (fun i => Fin.castAdd (q + q) (tailIndex p p i))
      (fun j => Fin.natAdd (p + p) (tailIndex q q j)))

/-- The label bijection between the product of strict forms and the strict
form of the product. -/
def prodLabel (p q : ℕ) : Fin ((p + p) + (q + q)) ≃ Fin ((q + p) + (q + p)) where
  toFun := prodLabelFun p q
  invFun := prodLabelInv p q
  left_inv j := by
    induction j using Fin.addCases with
    | left j =>
      rcases block_cases p p j with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
        simp only [prodLabelFun, prodLabelInv, Fin.append_left, join_head, join_tail]
    | right j =>
      rcases block_cases q q j with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
        simp only [prodLabelFun, prodLabelInv, Fin.append_right, join_head, join_tail]
  right_inv i := by
    rcases block_cases (q + p) (q + p) i with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      rcases block_cases q p i with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp only [prodLabelFun, prodLabelInv, Fin.append_left, Fin.append_right, join_head, join_tail]

theorem prodLabel_apply (p q : ℕ) (j : Fin ((p + p) + (q + q))) :
    prodLabel p q j = prodLabelFun p q j := rfl

omit [M ⊨ Axioms.ACVF] in
/-- The strict encoding of a product tuple, read through `prodLabel`, is the
pair of strict encodings of the two blocks. -/
theorem encode_prodLabel {p q : ℕ} (u : Fin (q + p) → M) :
    encode u ∘ prodLabel p q =
      Fin.append (encode (u ∘ headIndex q p)) (encode (u ∘ tailIndex q p)) := by
  funext j
  induction j using Fin.addCases with
  | left j =>
    rcases block_cases p p j with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp only [Function.comp_apply, prodLabel_apply, prodLabelFun, Fin.append_left, join_head,
        join_tail, encode]
  | right j =>
    rcases block_cases q q j with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp only [Function.comp_apply, prodLabel_apply, prodLabelFun, Fin.append_right, join_head,
        join_tail, encode]

end Blocks

/-! ### Lifts of strict charts and of products -/

section Lift
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section4.FiniteTupleBlocks DiamondIntegral.Section4.RVRealProducts
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.StrictCharts
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section6.DiamondLift DiamondIntegral.Section6.DiamondProduct

variable (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}

/-- Membership in the lift of the measured object of a chart. -/
theorem mem_rvLift_toObject {k : ℕ} (c : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k)
    (x : Fin k → VF M) (t : Fin c.arity → RVInfinity M) :
    (x, t) ∈ (rvLift (toObject hc c)).carrier ↔
      rvValues t ∈ c.domain ∧
        c.coordinate (rvValues t) = rvValues (SpecialTransformations.Section4.tupleRV x) := by
  constructor
  · rintro ⟨u, hu, hv⟩
    change u.val = t at hu
    subst hu
    exact ⟨u.property, (toObject_value hc c u).symm.trans (congrArg rvValues hv)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨t, h1⟩, rfl, rvValues_injective ((toObject_value hc c ⟨t, h1⟩).trans h2)⟩

/-- The lifted form of the measured object of a chart is the chart volume of
the labels. -/
theorem lift_form_value {k : ℕ} (c : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k)
    (hP : ProperInvariant S (rvLift (toMeasured hc c).object).carrier)
    (x : Fin k → VF M) (t : Fin c.arity → RVInfinity M)
    (h : (x, t) ∈ (rvLift (toMeasured hc c).object).carrier) :
    gammaMapValue (liftObject (toMeasured hc c) hP).form ⟨(x, t), h⟩ = c.volume (rvValues t) := rfl

variable (h00 : M ⊨ Axioms.ACVF00)

/-- Membership in the lift of the strict form of a chart. -/
theorem mem_rvLift_strict {k : ℕ} (c : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k)
    (x : Fin k → VF M) (t : Fin (c.arity + c.arity) → RVInfinity M) :
    (x, t) ∈ (rvLift (toObject hc (strictChart h00 c))).carrier ↔
      ∃ u ∈ c.domain, rvValues t = encode u ∧
        c.coordinate u = rvValues (SpecialTransformations.Section4.tupleRV x) := by
  refine (mem_rvLift_toObject hc (strictChart h00 c) x t).trans ?_
  constructor
  · rintro ⟨⟨u, hu, he⟩, hcoord⟩
    refine ⟨u, hu, he.symm, ?_⟩
    have hco : c.coordinate (decode (rvValues t)) =
        rvValues (SpecialTransformations.Section4.tupleRV x) := hcoord
    rwa [← he, decode_encode h00] at hco
  · rintro ⟨u, hu, he, hcoord⟩
    refine ⟨⟨u, hu, he.symm⟩, ?_⟩
    change c.coordinate (decode (rvValues t)) = _
    rw [he, decode_encode h00]
    exact hcoord

/-- Raw form of the label comparison: a strict encoded point of the product
chart is the same as a pair of strict encoded points of the factors, read
through `prodLabel`. -/
theorem product_mem_iff {B : GammaParameters.Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (z : Fin (l + k) → M) (w : Fin ((b.arity + a.arity) + (b.arity + a.arity)) → M) :
    (∃ u ∈ productSet a.domain b.domain, w = encode u ∧ productMap a.coordinate b.coordinate u = z) ↔
      (∃ ua ∈ a.domain, (w ∘ prodLabel a.arity b.arity) ∘ Fin.castAdd (b.arity + b.arity) = encode ua ∧
          a.coordinate ua = z ∘ headIndex l k) ∧
        (∃ ub ∈ b.domain, (w ∘ prodLabel a.arity b.arity) ∘ Fin.natAdd (a.arity + a.arity) = encode ub ∧
          b.coordinate ub = z ∘ tailIndex l k) := by
  constructor
  · rintro ⟨u, ⟨hua, hub⟩, rfl, hz⟩
    have he := encode_prodLabel (M := M) (p := a.arity) (q := b.arity) u
    refine ⟨⟨u ∘ headIndex b.arity a.arity, hua, ?_, ?_⟩, ⟨u ∘ tailIndex b.arity a.arity, hub, ?_, ?_⟩⟩
    · rw [he]
      exact funext (Fin.append_left _ _)
    · rw [← hz]
      exact (join_comp_head l k _ _).symm
    · rw [he]
      exact funext (Fin.append_right _ _)
    · rw [← hz]
      exact (join_comp_tail l k _ _).symm
  · rintro ⟨⟨ua, hua, hwa, hza⟩, ⟨ub, hub, hwb, hzb⟩⟩
    have hhead : join b.arity a.arity ua ub ∘ headIndex b.arity a.arity = ua := join_comp_head _ _ _ _
    have htail : join b.arity a.arity ua ub ∘ tailIndex b.arity a.arity = ub := join_comp_tail _ _ _ _
    refine ⟨join b.arity a.arity ua ub, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hhead]
      exact hua
    · rw [htail]
      exact hub
    · have h1 : w ∘ prodLabel a.arity b.arity =
          encode (join b.arity a.arity ua ub) ∘ prodLabel a.arity b.arity := by
        rw [encode_prodLabel, hhead, htail, ← hwa, ← hwb]
        exact Fin.append_castAdd_natAdd.symm
      funext i
      have := congrFun h1 ((prodLabel a.arity b.arity).symm i)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using this
    · change join l k (a.coordinate (join b.arity a.arity ua ub ∘ headIndex b.arity a.arity))
        (b.coordinate (join b.arity a.arity ua ub ∘ tailIndex b.arity a.arity)) = z
      rw [hhead, htail, hza, hzb]
      exact join_reconstruct l k z

section Main
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (T : LRV.Substructure M) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

/-- **The lift of a product chart is the product of the lifts.** For bounded
charts `a` of degree `k` and `b` of degree `l`, the lift of `a × b` (degree
`l + k`) is isomorphic in `μVF^◇[l + k]` to the product of the lifts of `a`
and `b` (degree `k + l`), transported along `k + l = l + k`. In value order
both objects carry the `a`-coordinates first; the isomorphism is the identity
on VF coordinates and permutes the labels by `prodLabel`. -/
theorem lift_product_isomorphic {k l : ℕ} (a : Obj (BT T) k) (b : Obj (BT T) l) :
    Isomorphic G
      (liftObject (dbObj hc h00 hκ hs T hsmall hΓ (RVBoundedCharts.product a b)).1
        (measuredRVLift_properInvariant h00 hc hκ hs hv _
          (dbObj hc h00 hκ hs T hsmall hΓ (RVBoundedCharts.product a b)).2))
      ((Nat.add_comm k l) ▸ DiamondProduct.VFObject.product hc
        (liftObject (dbObj hc h00 hκ hs T hsmall hΓ a).1
          (measuredRVLift_properInvariant h00 hc hκ hs hv _ (dbObj hc h00 hκ hs T hsmall hΓ a).2))
        (liftObject (dbObj hc h00 hκ hs T hsmall hΓ b).1
          (measuredRVLift_properInvariant h00 hc hκ hs hv _ (dbObj hc h00 hκ hs T hsmall hΓ b).2))) := by
  refine relabel_isomorphic_cast h00 hc lin hκ hs hv hsmall hΓ (Nat.add_comm k l) _ _
    (prodLabel a.arity b.arity) (fun x t => ?_) (fun x t hA hB => ?_)
  · refine (mem_rvLift_strict hc h00 (RVMeasuredProduct.product a.toChart b.toChart) x t).trans ?_
    refine (product_mem_iff a.toChart b.toChart _ _).trans ?_
    refine Iff.trans ?_ (mem_mixedProductDomain _ _ _).symm
    have hxa : rvValues (SpecialTransformations.Section4.tupleRV ((x ∘ Fin.cast (Nat.add_comm k l)) ∘
        Fin.castAdd l)) = rvValues (SpecialTransformations.Section4.tupleRV x) ∘ headIndex l k := by
      funext i
      simp only [rvValues, SpecialTransformations.Section4.tupleRV, Function.comp_apply, cast_castAdd]
    have hxb : rvValues (SpecialTransformations.Section4.tupleRV ((x ∘ Fin.cast (Nat.add_comm k l)) ∘
        Fin.natAdd k)) = rvValues (SpecialTransformations.Section4.tupleRV x) ∘ tailIndex l k := by
      funext i
      simp only [rvValues, SpecialTransformations.Section4.tupleRV, Function.comp_apply, cast_natAdd]
    refine and_congr ?_ ?_
    · refine Iff.trans ?_ (mem_rvLift_strict hc h00 a.toChart _ _).symm
      rw [hxa]
      rfl
    · refine Iff.trans ?_ (mem_rvLift_strict hc h00 b.toChart _ _).symm
      rw [hxb]
      rfl
  · obtain ⟨u, _, hw, _⟩ :=
      (mem_rvLift_strict hc h00 (RVMeasuredProduct.product a.toChart b.toChart) x t).mp hA
    have he := encode_prodLabel (M := M) (p := a.arity) (q := b.arity) u
    have hwa : rvValues ((t ∘ prodLabel a.arity b.arity) ∘ Fin.castAdd (b.arity + b.arity)) =
        encode (u ∘ headIndex b.arity a.arity) := by
      change (rvValues t ∘ prodLabel a.arity b.arity) ∘ Fin.castAdd (b.arity + b.arity) = _
      rw [hw, he]
      exact funext (Fin.append_left _ _)
    have hwb : rvValues ((t ∘ prodLabel a.arity b.arity) ∘ Fin.natAdd (a.arity + a.arity)) =
        encode (u ∘ tailIndex b.arity a.arity) := by
      change (rvValues t ∘ prodLabel a.arity b.arity) ∘ Fin.natAdd (a.arity + a.arity) = _
      rw [hw, he]
      exact funext (Fin.append_right _ _)
    refine (lift_form_value hc _ _ x t hA).trans
      (Eq.trans ?_ (productForm_value hc _ _ _ _ hB).symm)
    refine Eq.trans ?_ (congrArg₂ (· * ·) (lift_form_value hc _ _ _ _ _).symm
      (lift_form_value hc _ _ _ _ _).symm)
    change (RVMeasuredProduct.product a.toChart b.toChart).volume (decode (rvValues t)) =
      a.volume (decode (rvValues ((t ∘ prodLabel a.arity b.arity) ∘ Fin.castAdd (b.arity + b.arity)))) *
        b.volume (decode (rvValues ((t ∘ prodLabel a.arity b.arity) ∘ Fin.natAdd (a.arity + a.arity))))
    rw [hwa, hwb, decode_encode h00, decode_encode h00, hw, decode_encode h00]
    rfl

omit [LRV.Structure M] [M ⊨ Axioms.ACVF] in
/-- Transport along a degree equation does not change the graded element. -/
theorem sigma_mk_cast {X : ℕ → Type} {n m : ℕ} (h : n = m) (Y : X n) :
    (⟨m, h ▸ Y⟩ : Σ j, X j) = ⟨n, Y⟩ := by
  subst h
  rfl

/-- **Graded form.** As elements of `Σ n, μVF^◇[n]`, the lift of `a × b` is
isomorphic (in its degree `l + k`) to an object that is literally the
product of the lifts, placed in degree `k + l`. -/
theorem lift_product_sigma {k l : ℕ} (a : Obj (BT T) k) (b : Obj (BT T) l) :
    ∃ Z : VFObject (M := M) (T : Set M) (l + k),
      Isomorphic G
        (liftObject (dbObj hc h00 hκ hs T hsmall hΓ (RVBoundedCharts.product a b)).1
          (measuredRVLift_properInvariant h00 hc hκ hs hv _
            (dbObj hc h00 hκ hs T hsmall hΓ (RVBoundedCharts.product a b)).2)) Z ∧
      (⟨l + k, Z⟩ : Σ n, VFObject (M := M) (T : Set M) n) =
        ⟨k + l, DiamondProduct.VFObject.product hc
          (liftObject (dbObj hc h00 hκ hs T hsmall hΓ a).1
            (measuredRVLift_properInvariant h00 hc hκ hs hv _ (dbObj hc h00 hκ hs T hsmall hΓ a).2))
          (liftObject (dbObj hc h00 hκ hs T hsmall hΓ b).1
            (measuredRVLift_properInvariant h00 hc hκ hs hv _ (dbObj hc h00 hκ hs T hsmall hΓ b).2))⟩ :=
  ⟨_, lift_product_isomorphic hc h00 hκ hs T hsmall hΓ hv a b,
    sigma_mk_cast (X := fun j => VFObject (M := M) (T : Set M) j) (Nat.add_comm k l) _⟩

end Main

end Lift

end DiamondIntegral.Section7.LiftProducts
