import «section 7».SpecialStep

/-! Lemma 7.11 (`special:to:blowup:coa`), toward chains.

A bijection between tagged RV-pullback sets that maps whole label fibres to
whole label fibres, preserves the VF leading terms and transports the forms
induces an isomorphism of the contractions in `μRV^db` (`contractionIso`).
Regularization of a tagged set is such a bijection, so it does not change the
contraction up to isomorphism (`regularization_matching`). These are the steps
of a special covariant chain that add labels without blowing up. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.SpecialChains
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.ChartOfMeasured

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

/-! ### Contractions along label-fibre matchings -/

section Matching
variable {X : DefSet (rawMixedSpace (M := M) n r) S} {Y : DefSet (rawMixedSpace (M := M) n s) S}
variable (hTX : ∀ p ∈ X.carrier, ∀ q ∈ X.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
  (hRX : IsRVPullback X.carrier)
  (hFX : ∀ a : Fin n → VF M, {u : Fin r → RVInfinity M | (a, u) ∈ X.carrier}.Finite)
  (hDX : VFDoublyBounded X.carrier)
  (ωX : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)) (hωX : ∀ p q : X, p.val.2 = q.val.2 → ωX p = ωX q)
variable (hTY : ∀ p ∈ Y.carrier, ∀ q ∈ Y.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
  (hRY : IsRVPullback Y.carrier)
  (hFY : ∀ a : Fin n → VF M, {u : Fin s → RVInfinity M | (a, u) ∈ Y.carrier}.Finite)
  (hDY : VFDoublyBounded Y.carrier)
  (ωY : Map Y (DefSet.univ (rawGammaPresentation (M := M)) S)) (hωY : ∀ p q : Y, p.val.2 = q.val.2 → ωY p = ωY q)

/-- A label-fibre matching bijection preserving leading terms and forms
induces an isomorphism of the contractions. -/
def contractionIso (f : Map X Y) (hf : Function.Bijective f) (hm : MapsWholeTagFibres f)
    (hlead : ∀ p : X, tupleRV M (f p).val.1 = tupleRV M p.val.1)
    (hform : ∀ p : X, ωY (f p) = ωX p) :
    MeasuredRVIso (contractedMeasuredRVObject X hTX hRX hFX hDX ωX hωX)
      (contractedMeasuredRVObject Y hTY hRY hFY hDY ωY hωY) := by
  refine ⟨rvIsoOfFiniteFibres (pureRVTagMatchingMap f hm) (pureRVTagMatchingMap_bijective f hf hm)
    (contractedMeasuredRVObject X hTX hRX hFX hDX ωX hωX).finiteVolume
    (contractedMeasuredRVObject Y hTY hRY hFY hDY ωY hωY).finiteVolume
    (contractedMeasuredRVObject X hTX hRX hFX hDX ωX hωX).nonzero
    (contractedMeasuredRVObject Y hTY hRY hFY hDY ωY hωY).nonzero, fun u => ?_⟩
  obtain ⟨p, rfl⟩ := pureRVTagQuotient_surjective X u
  rw [rvIsoOfFiniteFibres_map, pureRVTagMatchingMap_commutes]
  unfold MeasuredRVObject.totalWeight
  have hv : (contractedMeasuredRVObject X hTX hRX hFX hDX ωX hωX).object.value (pureRVTagQuotient X p) =
      (contractedMeasuredRVObject Y hTY hRY hFY hDY ωY hωY).object.value (pureRVTagQuotient Y (f p)) := by
    change (preparedRVObject X hTX).value (pureRVTagQuotient X p) = (preparedRVObject Y hTY).value (pureRVTagQuotient Y (f p))
    rw [preparedRVObject_value, preparedRVObject_value, hlead]
  rw [volumeGamma_congr hv, contractedMeasuredRVObject_form, contractedMeasuredRVObject_form]
  congr 1
  exact (congrArg Subtype.val (hform p)).symm

end Matching

/-! ### Regularization -/

section Regularization
variable (X : DefSet (rawMixedSpace (M := M) n r) S)

theorem regularize_fst (p : Mixed M n r) : (regularize p).1 = p.1 := rfl

theorem regularize_snd_left (p : Mixed M n r) (i : Fin n) :
    (regularize p).2 (Fin.castAdd r i) = rv M (p.1 i) := by
  simp only [regularize, Fin.append_left]
  rfl

theorem regularize_snd_right (p : Mixed M n r) (i : Fin r) : (regularize p).2 (Fin.natAdd n i) = p.2 i := by
  simp only [regularize, Fin.append_right]

theorem regularize_snd_eq {p q : Mixed M n r} :
    (regularize p).2 = (regularize q).2 ↔ tupleRV M p.1 = tupleRV M q.1 ∧ p.2 = q.2 := by
  constructor
  · intro h
    refine ⟨funext (fun i => ?_), funext (fun i => ?_)⟩
    · have := congrFun h (Fin.castAdd r i)
      rwa [regularize_snd_left, regularize_snd_left] at this
    · have := congrFun h (Fin.natAdd n i)
      rwa [regularize_snd_right, regularize_snd_right] at this
  · rintro ⟨h1, h2⟩
    simp only [regularize]
    rw [h1, h2]

theorem mem_regularize {q : Mixed M n (n + r)} :
    q ∈ (regularizeMap X).image.carrier ↔ ∃ p ∈ X.carrier, regularize p = q := by
  rw [regularization_carrier]
  rfl

/-- The regularization is tagged. -/
theorem regularize_tagged : ∀ p ∈ (regularizeMap X).image.carrier, ∀ q ∈ (regularizeMap X).image.carrier,
    p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  intro p hp q hq he
  obtain ⟨p', _, rfl⟩ := (mem_regularize X).mp hp
  obtain ⟨q', _, rfl⟩ := (mem_regularize X).mp hq
  exact (regularize_snd_eq.mp he).1

/-- The regularization of an RV pullback is an RV pullback. -/
theorem regularize_pullback (hR : IsRVPullback X.carrier) : IsRVPullback (regularizeMap X).image.carrier := by
  show rvHull _ = _
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨p, hp, h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
    obtain ⟨p', hp', rfl⟩ := (mem_regularize X).mp hp
    apply (mem_regularize X).mpr
    have hrv : tupleRV M p'.1 = tupleRV M q.1 := h1
    have hq' : (q.1, p'.2) ∈ X.carrier := rvPullback_mem_of_sameRV hR hp' hrv rfl
    refine ⟨(q.1, p'.2), hq', ?_⟩
    refine Prod.ext rfl ?_
    rw [← h2]
    show Fin.append (tupleRV M q.1) p'.2 = Fin.append (tupleRV M p'.1) p'.2
    rw [hrv]
  · intro q hq
    exact (mem_rvHull_iff _ q).mpr ⟨q, hq, rfl, rfl⟩

/-- Regularization keeps finite RV fibres. -/
theorem regularize_finite (hF : ∀ a : Fin n → VF M, {u : Fin r → RVInfinity M | (a, u) ∈ X.carrier}.Finite) :
    ∀ a : Fin n → VF M, {u : Fin (n + r) → RVInfinity M | (a, u) ∈ (regularizeMap X).image.carrier}.Finite := by
  intro a
  apply ((hF a).image (fun u => Fin.append (tupleRV M a) u)).subset
  intro u hu
  obtain ⟨p, hp, he⟩ := (mem_regularize X).mp hu
  have h1 : p.1 = a := congrArg Prod.fst he
  refine ⟨p.2, ?_, ?_⟩
  · change (a, p.2) ∈ X.carrier
    rw [← h1]
    exact hp
  · have h2 := congrArg Prod.snd he
    change Fin.append (tupleRV M p.1) p.2 = u at h2
    rw [h1] at h2
    exact h2

theorem regularize_vfDoublyBounded (hD : VFDoublyBounded X.carrier) : VFDoublyBounded (regularizeMap X).image.carrier := by
  obtain ⟨γ, hγ⟩ := hD
  refine ⟨γ, fun p hp i => ?_⟩
  obtain ⟨q, hq, rfl⟩ := (mem_regularize X).mp hp
  exact hγ q hq i

/-- On a tagged set, regularization maps whole label fibres to whole label
fibres. -/
theorem regularization_matching
    (hT : ∀ p ∈ X.carrier, ∀ q ∈ X.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    MapsWholeTagFibres (regularization X) := by
  intro p b
  constructor
  · intro hb
    obtain ⟨a, rfl⟩ := (regularization_bijective X).2 b
    refine ⟨a, (regularize_snd_eq.mp hb).2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact regularize_snd_eq.mpr ⟨hT _ a.property _ p.property ha, ha⟩

end Regularization

/-! ### Zero-centred steps are trivial on VF doubly bounded sets -/

section ZeroCentered
variable {X : DefSet (rawMixedSpace (M := M) n r) S} (Z : ZeroCenteredData X)

/-- On a VF doubly bounded set the zero-centred core is empty: invariance at the
radius of the centre would move a deeper coordinate to `0`. -/
theorem zc_core_false (hD : VFDoublyBounded X.carrier) {p : Mixed M n r} (hp : p ∈ X.carrier) (i : Fin n) :
    Z.core p i = false := by
  by_contra h
  have hlt : vfValue Z.center < vfValue (p.1 i) := of_decide_eq_true (Bool.eq_true_of_not_eq_false h)
  let y := Function.update p.1 i 0
  have hcong : Congruent (fun _ => finiteValue Z.center Z.center_nonzero) p.1 y := by
    intro l
    by_cases hl : l = i
    · rw [hl]
      change vfValue Z.center < vfValue (p.1 i - Function.update p.1 i 0 i)
      rw [Function.update_self, sub_zero]
      exact hlt
    · change (finiteValue Z.center Z.center_nonzero).val < Values.vfValueHom (p.1 l - Function.update p.1 i 0 l)
      rw [Function.update_of_ne hl, sub_self]
      exact SpecialTransformations.Section9.gamma_lt_value_zero _
  have hy : y ∈ vfFibre X.carrier p.2 := (Z.invariant p.2 p.1 y hcong).mp hp
  exact hD.nonzero hy i (Function.update_self _ _ _)

/-- On a VF doubly bounded set the zero-centred point map only adds the tags
`rv(1)`. -/
theorem zc_point (hD : VFDoublyBounded X.carrier) {p : Mixed M n r} (hp : p ∈ X.carrier) :
    Z.point p = (p.1, Fin.append (fun _ : Fin n => branchTag (M := M) false) p.2) := by
  have hcore : Z.core p = fun _ => false := funext (zc_core_false Z hD hp)
  simp only [ZeroCenteredData.point, ZeroCenteredData.tags, hcore]
  congr 1
  funext i
  simp [ZeroCenteredData.shift]

end ZeroCentered

/-! ### The invariant of a special covariant chain and its class -/

section Classes
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.IsoOfMeasured
variable (hc : CanonicalStructure.IsCanonical (M := M)) (T : LRV.Substructure M)

/-- The invariant of the sets in a special covariant chain starting at a lift:
an RV pullback with finite RV fibres, doubly bounded, with a form constant on
label fibres. -/
structure Good (X : DefSet (rawMixedSpace (M := M) n r) (T : Set M)) where
  pullback : IsRVPullback X.carrier
  finite : ∀ a : Fin n → VF M, {u : Fin r → RVInfinity M | (a, u) ∈ X.carrier}.Finite
  vfBounded : VFDoublyBounded X.carrier
  rvBounded : RVSupportDoublyBounded X.carrier
  form : Map X (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))
  form_labels : ∀ p q : X, p.val.2 = q.val.2 → form p = form q

variable {T} {X : DefSet (rawMixedSpace (M := M) n r) (T : Set M)}

/-- The form on the regularization. -/
def regForm (g : Good T X) : Map (regularizeMap X).image (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)) :=
  g.form.comp ((regularization X).inverse (regularization_bijective X))

theorem regForm_apply (g : Good T X) (p : X) : regForm g (regularization X p) = g.form p := by
  change g.form ((regularization X).inverse _ (regularization X p)) = _
  rw [Map.inverse_apply]

theorem regForm_labels (g : Good T X) (p q : (regularizeMap X).image) (he : p.val.2 = q.val.2) :
    regForm g p = regForm g q := by
  obtain ⟨a, rfl⟩ := (regularization_bijective X).2 p
  obtain ⟨b, rfl⟩ := (regularization_bijective X).2 q
  rw [regForm_apply, regForm_apply]
  exact g.form_labels a b (regularize_snd_eq.mp he).2

theorem reg_rvBounded (g : Good T X) : RVSupportDoublyBounded (regularizeMap X).image.carrier := by
  obtain ⟨γ, hγ⟩ := g.vfBounded
  obtain ⟨δ, hδ⟩ := g.rvBounded
  have h1 : ((max γ δ)⁻¹).val ≤ (γ⁻¹).val := show (max γ δ)⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left _ _)
  have h2 : ((max γ δ)⁻¹).val ≤ (δ⁻¹).val := show (max γ δ)⁻¹ ≤ δ⁻¹ from inv_le_inv' (le_max_right _ _)
  have h3 : γ.val ≤ (max γ δ).val := show γ ≤ max γ δ from le_max_left _ _
  have h4 : δ.val ≤ (max γ δ).val := show δ ≤ max γ δ from le_max_right _ _
  refine ⟨max γ δ, fun p hp i => ?_⟩
  obtain ⟨q, hq, rfl⟩ := (mem_regularize X).mp hp
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [regularize_snd_left]
    obtain ⟨hl, hu⟩ := hγ q hq i
    exact ⟨h1.trans hl, hu.trans h3⟩
  · rw [regularize_snd_right]
    obtain ⟨hl, hu⟩ := hδ q hq i
    exact ⟨h2.trans hl, hu.trans h4⟩

/-- The contraction of the regularization. -/
def regC (g : Good T X) : MeasuredRVObject (M := M) (T : Set M) n :=
  contractedMeasuredRVObject (regularizeMap X).image (regularize_tagged X) (regularize_pullback X g.pullback)
    (regularize_finite X g.finite) (regularize_vfDoublyBounded X g.vfBounded) (regForm g) (regForm_labels g)

theorem regC_db (g : Good T X) : (regC g).doublyBounded :=
  contractedMeasuredRVObject_doublyBounded _ _ _ _ _ (reg_rvBounded g) _ _

/-- The Section 7 class of a set of a chain. -/
def clsG (g : Good T X) : Cls (BT T) n := cls (objOf hc T (regC g) (regC_db g))

theorem cls_objOf_eq {U V : MeasuredRVObject (M := M) (T : Set M) n} (hU : U.doublyBounded) (hV : V.doublyBounded)
    (e : MeasuredRVIso U V) : cls (objOf hc T U hU) = cls (objOf hc T V hV) :=
  (cls_eq_iff_measured hc).mpr ⟨((measuredIso_chartOf hc U).comp e).comp (measuredIso_chartOf hc V).symm⟩

/-- The regularization of a set of a chain. -/
def regGood (g : Good T X) : Good T (regularizeMap X).image :=
  ⟨regularize_pullback X g.pullback, regularize_finite X g.finite, regularize_vfDoublyBounded X g.vfBounded,
    reg_rvBounded g, regForm g, regForm_labels g⟩

/-- Regularization does not change the class. -/
theorem clsG_reg (g : Good T X) : clsG hc (regGood g) = clsG hc g := by
  symm
  apply cls_objOf_eq hc
  exact contractionIso _ _ _ _ _ _ _ _ _ _ _ _ (regularization (regularizeMap X).image)
    (regularization_bijective _) (regularization_matching _ (regularize_tagged X)) (fun _ => rfl)
    (fun p => regForm_apply (regGood g) p)

end Classes

/-! ### Zero-centred steps keep the class -/

section ZeroCenteredClass
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.LiftClasses
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M}
variable {X : DefSet (rawMixedSpace (M := M) n r) (T : Set M)} (g : Good T X) (Z : ZeroCenteredData X)
variable (h00 : M ⊨ Axioms.ACVF00)

include g in
theorem mem_zc {q : Mixed M n (n + r)} :
    q ∈ Z.map.image.carrier ↔ ∃ p ∈ X.carrier, q = (p.1, Fin.append (fun _ : Fin n => branchTag (M := M) false) p.2) := by
  rw [ZeroCenteredData.image_carrier]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, zc_point Z g.vfBounded hp⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, zc_point Z g.vfBounded hp⟩

theorem append_ones_injective {u v : Fin r → RVInfinity M}
    (h : Fin.append (fun _ : Fin n => branchTag (M := M) false) u = Fin.append (fun _ : Fin n => branchTag (M := M) false) v) :
    u = v := funext (fun i => by simpa only [Fin.append_right] using congrFun h (Fin.natAdd n i))

include h00 in
/-- The image of a zero-centred step, with the transported form. -/
def zcGood : Good T Z.map.image where
  pullback := by
    show rvHull _ = _
    apply Set.Subset.antisymm
    · intro q hq
      obtain ⟨q', hq', h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
      obtain ⟨p, hp, rfl⟩ := (mem_zc g Z).mp hq'
      apply (mem_zc g Z).mpr
      refine ⟨(q.1, p.2), rvPullback_mem_of_sameRV g.pullback hp h1 rfl, ?_⟩
      exact Prod.ext rfl h2.symm
    · intro q hq
      exact (mem_rvHull_iff _ q).mpr ⟨q, hq, rfl, rfl⟩
  finite := by
    intro a
    apply ((g.finite a).image (fun u => Fin.append (fun _ : Fin n => branchTag (M := M) false) u)).subset
    intro v hv
    obtain ⟨p, hp, he⟩ := (mem_zc g Z).mp hv
    have h1 : p.1 = a := (congrArg Prod.fst he).symm
    refine ⟨p.2, ?_, (congrArg Prod.snd he).symm⟩
    change (a, p.2) ∈ X.carrier
    rw [← h1]
    exact hp
  vfBounded := by
    obtain ⟨γ, hγ⟩ := g.vfBounded
    refine ⟨γ, fun q hq i => ?_⟩
    obtain ⟨p, hp, rfl⟩ := (mem_zc g Z).mp hq
    exact hγ p hp i
  rvBounded := by
    obtain ⟨δ, hδ⟩ := g.rvBounded
    have h1 : ((max δ 1)⁻¹).val ≤ (δ⁻¹).val := show (max δ 1)⁻¹ ≤ δ⁻¹ from inv_le_inv' (le_max_left _ _)
    have h2 : δ.val ≤ (max δ 1).val := show δ ≤ max δ 1 from le_max_left _ _
    have h3 : ((max δ 1)⁻¹).val ≤ (1 : Values.Gamma (M := M)).val :=
      show (max δ 1)⁻¹ ≤ 1 from inv_le_one'.mpr (le_max_right _ _)
    have h4 : (1 : Values.Gamma (M := M)).val ≤ (max δ 1).val := show 1 ≤ max δ 1 from le_max_right _ _
    refine ⟨max δ 1, fun q hq i => ?_⟩
    obtain ⟨p, hp, rfl⟩ := (mem_zc g Z).mp hq
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

theorem zcGood_form (p : X) : (zcGood g Z h00).form (Z.bijection p) = g.form p := by
  change g.form (Z.bijection.inverse _ (Z.bijection p)) = _
  rw [Map.inverse_apply]

/-- A zero-centred step does not change the class. -/
theorem clsG_zc : clsG hc (zcGood g Z h00) = clsG hc g := by
  symm
  apply cls_objOf_eq hc
  let f : Map (regularizeMap X).image (regularizeMap Z.map.image).image :=
    (regularization Z.map.image).comp (Z.bijection.comp ((regularization X).inverse (regularization_bijective X)))
  have hinv : Function.Bijective ((regularization X).inverse (regularization_bijective X)) :=
    ⟨fun a b h => by
      have h' := congrArg (regularization X) h
      rwa [Map.apply_inverse, Map.apply_inverse] at h',
     fun a => ⟨regularization X a, Map.inverse_apply _ _ a⟩⟩
  have hf : Function.Bijective f := (regularization_bijective _).comp ((Z.bijective h00).comp hinv)
  have hfx : ∀ x : X, f (regularization X x) = regularization Z.map.image (Z.bijection x) := by
    intro x
    change regularization Z.map.image (Z.bijection ((regularization X).inverse _ (regularization X x))) = _
    rw [Map.inverse_apply]
  have hsnd : ∀ x : X, (f (regularization X x)).val.2 =
      Fin.append (tupleRV M x.val.1) (Fin.append (fun _ : Fin n => branchTag (M := M) false) x.val.2) := by
    intro x
    rw [hfx]
    change (regularize (Z.point x.val)).2 = _
    rw [zc_point Z g.vfBounded x.property]
    rfl
  refine contractionIso _ _ _ _ _ _ _ _ _ _ _ _ f hf ?_ ?_ ?_
  · intro p b
    obtain ⟨x, rfl⟩ := (regularization_bijective X).2 p
    obtain ⟨a, rfl⟩ := hf.2 b
    obtain ⟨y, rfl⟩ := (regularization_bijective X).2 a
    rw [hsnd, hsnd]
    constructor
    · intro he
      refine ⟨regularization X y, ?_, rfl⟩
      have h1 : tupleRV M y.val.1 = tupleRV M x.val.1 := funext (fun i => by
        simpa only [Fin.append_left] using congrFun he (Fin.castAdd _ i))
      have h2 : y.val.2 = x.val.2 := append_ones_injective (funext (fun i => by
        simpa only [Fin.append_right] using congrFun he (Fin.natAdd n i)))
      exact regularize_snd_eq.mpr ⟨h1, h2⟩
    · rintro ⟨a, ha, hfa⟩
      obtain ⟨z, rfl⟩ := (regularization_bijective X).2 a
      have hzy : z = y := (regularization_bijective X).1 (hf.1 hfa)
      subst hzy
      have he := regularize_snd_eq.mp ha
      have e1 : tupleRV M z.val.1 = tupleRV M x.val.1 := he.1
      have e2 : z.val.2 = x.val.2 := he.2
      exact congrArg₂ Fin.append e1 (congrArg (Fin.append _) e2)
  · intro p
    obtain ⟨x, rfl⟩ := (regularization_bijective X).2 p
    rw [hfx]
    change tupleRV M (Z.point x.val).1 = tupleRV M x.val.1
    rw [zc_point Z g.vfBounded x.property]
  · intro p
    obtain ⟨x, rfl⟩ := (regularization_bijective X).2 p
    rw [hfx, regForm_apply, regForm_apply, zcGood_form]

end ZeroCenteredClass

end DiamondIntegral.Section7.SpecialChains
