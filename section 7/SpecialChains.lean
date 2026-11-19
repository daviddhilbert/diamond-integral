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

end DiamondIntegral.Section7.SpecialChains
