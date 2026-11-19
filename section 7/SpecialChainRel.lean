import «section 7».SpecialChainSplit

/-! Lemma 7.11 (`special:to:blowup:coa`): a general relative step on a chain set.

The image of relative aperture data `R` on a chain set `X` is the union of the
image of its active part (`RelativeRestrict.restrictActive`) and of the
inactive part with the tag `rv(1)` added. Both pieces are chain sets; the
first is a blowup of length one of the active part of `X`
(`SpecialChainStep.step_rel_active`), and the second has the class of the
inactive part. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.SpecialChainRel
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.SpecialChains
open DiamondIntegral.Section7.SpecialChainSplit DiamondIntegral.Section7.SpecialChainStep
open DiamondIntegral.Section7.RelativeRestrict DiamondIntegral.Section7.MeasuredRVBridge

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n r : ℕ}

/-! ### Labels with a given tail -/

section Tail
variable {S : Set M} (J : DefSet (rawRVSpace (M := M) r) S)

theorem decode_tail {z : Fin (1 + r) → M} (hz : z ∈ (rawRVSpace (M := M) (1 + r)).domain)
    (hz' : (fun i => z (Fin.natAdd 1 i)) ∈ (rawRVSpace (M := M) r).domain) :
    (fun i => (rawRVSpace (M := M) (1 + r)).decode ⟨z, hz⟩ (Fin.natAdd 1 i)) =
      (rawRVSpace (M := M) r).decode ⟨_, hz'⟩ := by
  apply rvValues_injective
  have h1 := decode_rv ⟨z, hz⟩
  have h2 := decode_rv ⟨_, hz'⟩
  funext i
  have h3 := congrFun h1 (Fin.natAdd 1 i)
  have h4 := congrFun h2 i
  exact h3.trans h4.symm

theorem tailDef_definable : (rawRVSpace (M := M) (1 + r)).Definable S
    {L : Fin (1 + r) → RVInfinity M | (fun i => L (Fin.natAdd 1 i)) ∈ J.carrier} := by
  have h1 : S.Definable LRV ((rawRVSpace (M := M) r).preimage J.carrier) := J.definable
  have h2 := h1.preimage_comp (Fin.natAdd 1 : Fin r → Fin (1 + r))
  have h3 := ((rawRVSpace (M := M) (1 + r)).domain_definable).mono (Set.empty_subset S)
  change S.Definable LRV ((rawRVSpace (M := M) (1 + r)).preimage _)
  convert h3.inter h2 using 1
  ext z
  constructor
  · rintro ⟨hz, hJ⟩
    refine ⟨hz, ?_⟩
    have hz' : (fun i => z (Fin.natAdd 1 i)) ∈ (rawRVSpace (M := M) r).domain := by
      obtain ⟨t, ht⟩ := hz
      exact ⟨fun i => t (Fin.natAdd 1 i), funext (fun i => congrFun ht (Fin.natAdd 1 i))⟩
    refine ⟨hz', ?_⟩
    have hJ1 : (fun i => (rawRVSpace (M := M) (1 + r)).decode ⟨z, hz⟩ (Fin.natAdd 1 i)) ∈ J.carrier := hJ
    rw [decode_tail hz hz'] at hJ1
    exact hJ1
  · rintro ⟨hz, hz', hJ⟩
    refine ⟨hz, ?_⟩
    change (fun i => (rawRVSpace (M := M) (1 + r)).decode ⟨z, hz⟩ (Fin.natAdd 1 i)) ∈ J.carrier
    have hJ' : (rawRVSpace (M := M) r).decode ⟨fun i => z (Fin.natAdd 1 i), hz'⟩ ∈ J.carrier := hJ
    rw [decode_tail hz hz']
    exact hJ'

/-- The labels whose tail lies in `J`. -/
def tailDef : DefSet (rawRVSpace (M := M) (1 + r)) S := ⟨_, tailDef_definable J⟩

theorem mem_tailDef (L : Fin (1 + r) → RVInfinity M) :
    L ∈ (tailDef J).carrier ↔ (fun i => L (Fin.natAdd 1 i)) ∈ J.carrier := Iff.rfl

end Tail

/-! ### Auxiliary constructions -/

/-- A map with values in a smaller definable set. -/
def mapCorestrict {P Q : Space LRV M} {S : Set M} {A : DefSet P S} {B C : DefSet Q S} (f : Map A B)
    (h : ∀ a, (f a).val ∈ C.carrier) : Map A C where
  toFun a := ⟨(f a).val, h a⟩
  graph_definable := f.graph_definable

theorem clsG_congr (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M}
    {X X' : DefSet (rawMixedSpace (M := M) n r) (T : Set M)} (h : X = X') (g : Good T X) (g' : Good T X')
    (hform : ∀ p : X, g'.form ⟨p.val, h ▸ p.property⟩ = g.form p) : clsG hc g = clsG hc g' := by
  subst h
  have he : g = g' := by
    cases g
    cases g'
    congr
    apply Map.ext
    intro p
    exact (hform p).symm
  rw [he]

/-! ### The general relative step -/

section RelGeneral
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.ElementaryBlowups
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {k : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M)} (g : Good T X)
variable (R : DiamondIntegral.Section6.RelativeApertureData (G := G) X)
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk (T : Set M) < κ)
variable (h00 : M ⊨ Axioms.ACVF00)

/-- The active part, with the restricted data. -/
abbrev gA : Good T (focusActive X R.activeTags) := goodRes g R.activeTags
abbrev RA := RelativeRestrict.RelativeApertureData.restrictActive R

theorem point_snd_tail (p : Mixed M (1 + k) r) : (fun i => (R.point p).2 (Fin.natAdd 1 i)) = p.2 := by
  funext i
  simp only [DiamondIntegral.Section6.RelativeApertureData.point, Fin.append_right]

theorem mem_image {q : Mixed M (1 + k) (1 + r)} : q ∈ R.map.image.carrier ↔ ∃ p ∈ X.carrier, R.point p = q := by
  rw [DiamondIntegral.Section6.RelativeApertureData.image_carrier]
  rfl

/-- The image of the active part is the active piece of the image. -/
theorem active_image_eq :
    focusActive R.map.image (tailDef R.activeTags) = (RA R).map.image := by
  apply DefSet.eq_of_carrier_eq
  ext q
  rw [DiamondIntegral.Section6.RelativeApertureData.image_carrier]
  constructor
  · rintro ⟨hq, hJ⟩
    obtain ⟨p, hp, rfl⟩ := (mem_image R).mp hq
    have hpa : p.2 ∈ R.activeTags.carrier := by
      have := hJ
      rw [mem_tailDef, point_snd_tail] at this
      exact this
    exact ⟨p, ⟨hp, hpa⟩, RelativeRestrict.RelativeApertureData.restrictActive_point R ⟨hp, hpa⟩⟩
  · rintro ⟨p, hp, rfl⟩
    rw [RelativeRestrict.RelativeApertureData.restrictActive_point R hp]
    refine ⟨(mem_image R).mpr ⟨p, hp.1, rfl⟩, ?_⟩
    rw [mem_tailDef, point_snd_tail]
    exact hp.2

/-- The active part's image is a chain set (`SpecialChainStep.relGood`). -/
abbrev gRA : Good T (RA R).map.image :=
  relGood hc (gA g R) (RA R) (RelativeRestrict.RelativeApertureData.restrictActive_all R) hκ hs hsmall h00

/-- The image of a relative step, with the transported form. -/
def imageGood : Good T R.map.image where
  pullback := by
    show rvHull _ = _
    apply Set.Subset.antisymm
    · intro q hq
      obtain ⟨p', hp', h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
      obtain ⟨x, hx, rfl⟩ := (mem_image R).mp hp'
      by_cases ha : x.2 ∈ R.activeTags.carrier
      · have hxa : R.point x ∈ (RA R).map.image.carrier := by
          rw [DiamondIntegral.Section6.RelativeApertureData.image_carrier]
          exact ⟨x, ⟨hx, ha⟩, RelativeRestrict.RelativeApertureData.restrictActive_point R ⟨hx, ha⟩⟩
        have hqa := rvPullback_mem_of_sameRV (gRA hc g R hκ hs hsmall h00).pullback hxa h1 h2
        rw [DiamondIntegral.Section6.RelativeApertureData.image_carrier] at hqa
        obtain ⟨y, hy, he⟩ := hqa
        rw [RelativeRestrict.RelativeApertureData.restrictActive_point R hy] at he
        exact (mem_image R).mpr ⟨y, hy.1, he⟩
      · rw [RelativeRestrict.RelativeApertureData.point_inactive R ha] at h1 h2
        have hy : (q.1, x.2) ∈ X.carrier := rvPullback_mem_of_sameRV g.pullback hx h1 rfl
        refine (mem_image R).mpr ⟨(q.1, x.2), hy, ?_⟩
        rw [RelativeRestrict.RelativeApertureData.point_inactive R (p := (q.1, x.2)) ha]
        exact Prod.ext rfl h2
    · intro q hq
      exact (mem_rvHull_iff _ q).mpr ⟨q, hq, rfl, rfl⟩
  finite := by
    intro a
    apply (((gRA hc g R hκ hs hsmall h00).finite a).union
      ((g.finite a).image (fun u => Fin.append (fun _ : Fin 1 => branchTag (M := M) false) u))).subset
    intro L hL
    obtain ⟨x, hx, he⟩ := (mem_image R).mp hL
    by_cases ha : x.2 ∈ R.activeTags.carrier
    · left
      change (a, L) ∈ (RA R).map.image.carrier
      rw [DiamondIntegral.Section6.RelativeApertureData.image_carrier]
      exact ⟨x, ⟨hx, ha⟩, (RelativeRestrict.RelativeApertureData.restrictActive_point R ⟨hx, ha⟩).trans he⟩
    · right
      rw [RelativeRestrict.RelativeApertureData.point_inactive R ha] at he
      have h1 : x.1 = a := congrArg Prod.fst he
      refine ⟨x.2, ?_, congrArg Prod.snd he⟩
      change (a, x.2) ∈ X.carrier
      rw [← h1]
      exact hx
  vfBounded := R.image_vfDoublyBounded
  rvBounded := R.image_rvDoublyBounded
  form := g.form.comp (R.bijection.inverse (R.bijective h00))
  form_labels := by
    intro p q he
    obtain ⟨a, rfl⟩ := (R.bijective h00).2 p
    obtain ⟨b, rfl⟩ := (R.bijective h00).2 q
    change g.form (R.bijection.inverse _ (R.bijection a)) = g.form (R.bijection.inverse _ (R.bijection b))
    rw [Map.inverse_apply, Map.inverse_apply]
    apply g.form_labels
    have ha := point_snd_tail R a.val
    have hb := point_snd_tail R b.val
    have he' : (R.point a.val).2 = (R.point b.val).2 := he
    rw [← ha, ← hb, he']

theorem imageGood_form (x : X) : (imageGood hc g R hκ hs hsmall h00).form (R.bijection x) = g.form x := by
  change g.form (R.bijection.inverse _ (R.bijection x)) = _
  rw [Map.inverse_apply]

theorem tail_append_one (u : Fin r → RVInfinity M) :
    (fun i => Fin.append (fun _ : Fin 1 => branchTag (M := M) false) u (Fin.natAdd 1 i)) = u := by
  funext i
  simp only [Fin.append_right]

/-- The inactive piece of the image has the class of the inactive part. -/
theorem clsG_inactive :
    clsG hc (goodRes (imageGood hc g R hκ hs hsmall h00) (compl (tailDef R.activeTags))) =
      clsG hc (goodRes g (compl R.activeTags)) := by
  symm
  apply cls_objOf_eq hc
  let Y := focusActive X (compl R.activeTags)
  let Z := focusActive R.map.image (compl (tailDef R.activeTags))
  have hYX : Y.carrier ⊆ X.carrier := fun _ h => h.1
  have hT : ∀ y : Y, (R.bijection (Map.inclusion hYX y)).val ∈ Z.carrier := by
    intro y
    refine ⟨(R.bijection (Map.inclusion hYX y)).property, Set.mem_univ _, ?_⟩
    change ¬ ((fun i => (R.point y.val).2 (Fin.natAdd 1 i)) ∈ R.activeTags.carrier)
    rw [point_snd_tail]
    exact y.property.2.2
  let Tm : Map Y Z := mapCorestrict (R.bijection.comp (Map.inclusion hYX)) hT
  have hTval : ∀ y : Y, (Tm y).val = (y.val.1, Fin.append (fun _ : Fin 1 => branchTag (M := M) false) y.val.2) :=
    fun y => RelativeRestrict.RelativeApertureData.point_inactive R y.property.2.2
  have hTbij : Function.Bijective Tm := by
    constructor
    · intro a b he
      have h1 := congrArg Subtype.val he
      rw [hTval, hTval] at h1
      apply Subtype.ext
      have hfst := congrArg Prod.fst h1
      have h2 := congrArg (fun z : Mixed M (1 + k) (1 + r) => fun i => z.2 (Fin.natAdd 1 i)) h1
      have hsnd : a.val.2 = b.val.2 := by simpa only [tail_append_one] using h2
      exact Prod.ext hfst hsnd
    · intro z
      obtain ⟨x, hx, he⟩ := (mem_image R).mp z.property.1
      have hxi : x.2 ∉ R.activeTags.carrier := by
        have h := z.property.2.2
        rw [← he] at h
        change ¬ ((fun i => (R.point x).2 (Fin.natAdd 1 i)) ∈ R.activeTags.carrier) at h
        rw [point_snd_tail] at h
        exact h
      exact ⟨⟨x, hx, Set.mem_univ _, hxi⟩, Subtype.ext he⟩
  have hinv : Function.Bijective ((regularization Y).inverse (regularization_bijective Y)) :=
    ⟨fun a b h => by
      have h' := congrArg (regularization Y) h
      rwa [Map.apply_inverse, Map.apply_inverse] at h',
     fun a => ⟨regularization Y a, Map.inverse_apply _ _ a⟩⟩
  let f : Map (regularizeMap Y).image (regularizeMap Z).image :=
    (regularization Z).comp (Tm.comp ((regularization Y).inverse (regularization_bijective Y)))
  have hf : Function.Bijective f := (regularization_bijective _).comp (hTbij.comp hinv)
  have hfx : ∀ y : Y, f (regularization Y y) = regularization Z (Tm y) := by
    intro y
    change regularization Z (Tm ((regularization Y).inverse _ (regularization Y y))) = _
    rw [Map.inverse_apply]
  have hsnd : ∀ y : Y, (f (regularization Y y)).val.2 =
      Fin.append (tupleRV M y.val.1) (Fin.append (fun _ : Fin 1 => branchTag (M := M) false) y.val.2) := by
    intro y
    rw [hfx]
    change (regularize (Tm y).val).2 = _
    rw [hTval]
    rfl
  refine contractionIso _ _ _ _ _ _ _ _ _ _ _ _ f hf ?_ ?_ ?_
  · intro p b
    obtain ⟨x, rfl⟩ := (regularization_bijective Y).2 p
    obtain ⟨a, rfl⟩ := hf.2 b
    obtain ⟨y, rfl⟩ := (regularization_bijective Y).2 a
    rw [hsnd, hsnd]
    constructor
    · intro he
      refine ⟨regularization Y y, ?_, rfl⟩
      have h1 : tupleRV M y.val.1 = tupleRV M x.val.1 := funext (fun i => by
        simpa only [Fin.append_left] using congrFun he (Fin.castAdd _ i))
      have h2 : y.val.2 = x.val.2 := by
        have h3 := congrArg (fun L : Fin ((1 + k) + (1 + r)) → RVInfinity M =>
          fun i => L (Fin.natAdd (1 + k) (Fin.natAdd 1 i))) he
        simpa only [Fin.append_right] using h3
      exact regularize_snd_eq.mpr ⟨h1, h2⟩
    · rintro ⟨a, ha, hfa⟩
      obtain ⟨z, rfl⟩ := (regularization_bijective Y).2 a
      have hzy : z = y := (regularization_bijective Y).1 (hf.1 hfa)
      subst hzy
      have he := regularize_snd_eq.mp ha
      have e1 : tupleRV M z.val.1 = tupleRV M x.val.1 := he.1
      have e2 : z.val.2 = x.val.2 := he.2
      exact congrArg₂ Fin.append e1 (congrArg (Fin.append _) e2)
  · intro p
    obtain ⟨x, rfl⟩ := (regularization_bijective Y).2 p
    rw [hfx]
    change tupleRV M (Tm x).val.1 = tupleRV M x.val.1
    rw [hTval]
  · intro p
    obtain ⟨x, rfl⟩ := (regularization_bijective Y).2 p
    rw [hfx, regForm_apply, regForm_apply]
    change (imageGood hc g R hκ hs hsmall h00).form (R.bijection (Map.inclusion hYX x)) = g.form (Map.inclusion hYX x)
    rw [imageGood_form]

end RelGeneral

end DiamondIntegral.Section7.SpecialChainRel
