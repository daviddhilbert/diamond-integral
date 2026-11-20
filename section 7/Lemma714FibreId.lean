import «section 7».Lemma714SliceContr

/-! Lemma 7.14, part 41: identifications for the fibre step.

* `ispRel_ext`: `μIsp^db` passes along a base extension.
* `cls_fibre_ext`: fibre objects of two sets with the same fibre and form have
  extended classes, across bases (used for the fibres of slices).
* `hsObj_value`, `hsObj_form`: the head-start object at the labels of a point.
* `cls_fibre_slice`: the fibre of the pulled-back first-stage set at a good point
  `b` has the head-start class of the slice contraction data over `S⟨b⟩`.
* `pull_uniform`: a named radius preserving the fibres and the form of the
  pulled-back first-stage set. -/

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
open DiamondIntegral.Section7.Lemma714Head DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.BlowupCongruence
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.SpecialChains
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section7.FibreRestriction DiamondIntegral.Section7.KernelBaseChange
open DiamondIntegral.Section7.BaseExtension DiamondIntegral.Section7.FibreObjects DiamondIntegral.Section7.FibreComparison

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-! ### Base extension of `μIsp^db` -/

theorem ispRel_ext {B C : GammaParameters.Base (M := M)} (ht : Transfer B C) {m : ℕ} {x y : Cls B m}
    (h : IspRel x y) : IspRel (clsExt ht x) (clsExt ht y) := by
  by_cases hm : m = 0
  · subst hm
    rw [ispRel_zero] at h ⊢
    rw [h]
  · obtain ⟨j, rfl⟩ : ∃ j, m = 1 + j := ⟨m - 1, by omega⟩
    rw [ispRel_iff (rfl : 1 + j = 1 + j)] at h ⊢
    exact muIsp_ext ht h

theorem clsExt_castCls {B C : GammaParameters.Base (M := M)} (ht : Transfer B C) {m m' : ℕ} (h : m = m')
    (x : Cls B m) : clsExt ht (castCls h x) = castCls h (clsExt ht x) := by
  subst h
  rfl

/-! ### Fibre objects across bases -/

section FibreExt
variable (hc : CanonicalStructure.IsCanonical (M := M))

theorem cls_fibre_ext {T₁ T₂ : LRV.Substructure M} {m₁ m₂ r k : ℕ}
    (X₁ : DefSet (rawMixedSpace (M := M) m₁ r) (T₁ : Set M))
    (ω₁ : Map X₁ (DefSet.univ (rawGammaPresentation (M := M)) (T₁ : Set M))) (a₁ : Fin m₁ → VF M)
    (X₂ : DefSet (rawMixedSpace (M := M) m₂ r) (T₂ : Set M))
    (ω₂ : Map X₂ (DefSet.univ (rawGammaPresentation (M := M)) (T₂ : Set M))) (a₂ : Fin m₂ → VF M)
    (π : Fin k → Fin r) (hF₁) (hNZ₁) (hF₂) (hNZ₂)
    (ht : Transfer (BT (adjoin T₂ a₂)) (BT (adjoin T₁ a₁)))
    (hdom : ∀ u, (a₁, u) ∈ X₁.carrier ↔ (a₂, u) ∈ X₂.carrier)
    (hform : ∀ u (h₁ : (a₁, u) ∈ X₁.carrier) (h₂ : (a₂, u) ∈ X₂.carrier),
      (ω₁ ⟨(a₁, u), h₁⟩).val = (ω₂ ⟨(a₂, u), h₂⟩).val)
    (hU₁ : (fibreObject T₁ X₁ ω₁ a₁ π hF₁ hNZ₁).doublyBounded)
    (hU₂ : (fibreObject T₂ X₂ ω₂ a₂ π hF₂ hNZ₂).doublyBounded) :
    cls (objOf hc (adjoin T₁ a₁) (fibreObject T₁ X₁ ω₁ a₁ π hF₁ hNZ₁) hU₁) =
      clsExt ht (cls (objOf hc (adjoin T₂ a₂) (fibreObject T₂ X₂ ω₂ a₂ π hF₂ hNZ₂) hU₂)) := by
  rw [clsExt_cls]
  apply cls_eq_of_iso
  have hD : rawDom (fibreObject T₁ X₁ ω₁ a₁ π hF₁ hNZ₁) = rawDom (fibreObject T₂ X₂ ω₂ a₂ π hF₂ hNZ₂) := by
    rw [fibre_rawDom, fibre_rawDom]
    ext u
    exact ⟨fun ⟨t, ht', he⟩ => ⟨t, (hdom t).mp ht', he⟩, fun ⟨t, ht', he⟩ => ⟨t, (hdom t).mpr ht', he⟩⟩
  refine isoOfMap _ _ (fun u => u)
    (DiamondIntegral.Section4.RVCoordinateMaps.coordinate_graph_definable _ _ (chartOf hc (fibreObject T₁ X₁ ω₁ a₁ π hF₁ hNZ₁)).domain_definable
      (id : Fin r → Fin r)) ?_ ?_
  · change Set.BijOn (fun u => u) (rawDom (fibreObject T₁ X₁ ω₁ a₁ π hF₁ hNZ₁))
      (rawDom (fibreObject T₂ X₂ ω₂ a₂ π hF₂ hNZ₂))
    rw [hD]
    exact Set.bijOn_id _
  · intro w hw
    change w ∈ rawDom (fibreObject T₁ X₁ ω₁ a₁ π hF₁ hNZ₁) at hw
    rw [fibre_rawDom] at hw
    obtain ⟨t, ht₁, rfl⟩ := hw
    have ht₂ := (hdom t).mp ht₁
    change rawVol (fibreObject T₁ X₁ ω₁ a₁ π hF₁ hNZ₁) (rvValues t) *
        ∏ i, GammaParameters.codeValue (rawCoord (fibreObject T₁ X₁ ω₁ a₁ π hF₁ hNZ₁) (rvValues t) i) =
      rawVol (fibreObject T₂ X₂ ω₂ a₂ π hF₂ hNZ₂) (rvValues t) *
        ∏ i, GammaParameters.codeValue (rawCoord (fibreObject T₂ X₂ ω₂ a₂ π hF₂ hNZ₂) (rvValues t) i)
    rw [fibre_rawVol X₁ ω₁ π a₁ hF₁ hNZ₁ t ht₁, fibre_rawVol X₂ ω₂ π a₂ hF₂ hNZ₂ t ht₂,
      fibre_rawCoord X₁ ω₁ π a₁ hF₁ hNZ₁ t ht₁, fibre_rawCoord X₂ ω₂ π a₂ hF₂ hNZ₂ t ht₂, hform t ht₁ ht₂]

end FibreExt

end DiamondIntegral.Section7.Lemma714Reduce

/-! ### Values and forms of head-start objects -/

namespace DiamondIntegral.Section7.Lemma714Head
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {T : LRV.Substructure M} {r k : ℕ} {X : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)} {lab : Fin k → Fin r}
  (g : HGood X lab) (hT : ∀ p ∈ X.carrier, ∀ q ∈ X.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)

theorem hsObj_value {y : Fin 1 → VF M} {w : Fin r → RVInfinity M} (h : (y, w) ∈ X.carrier)
    (u : (hsObj g hT).object.domain) (hu : u.val = w) :
    (hsObj g hT).object.value u = Fin.append (fun _ : Fin 1 => rv M (y 0)) (fun i => w (lab i)) := by
  obtain ⟨e, he, het⟩ := exists_bundle_point (lab := lab) h
  let q : rvHeadStartBundle X k lab := ⟨_, he⟩
  have hq : u = pureRVTagQuotient _ q := Subtype.ext hu
  subst hq
  change (preparedRVObject (rvHeadStartBundle X k lab) _).value (pureRVTagQuotient _ q) = _
  rw [preparedRVObject_value]
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · have hl : l = 0 := Subsingleton.elim _ _
    subst hl
    simp only [Fin.append_left]
    change rv M ((Fin.append y e : Fin (1 + k) → VF M) (Fin.castAdd k 0)) = _
    rw [Fin.append_left]
  · simp only [Fin.append_right]
    change rv M ((Fin.append y e : Fin (1 + k) → VF M) (Fin.natAdd 1 l)) = _
    rw [Fin.append_right]
    exact congrFun het l

theorem hsObj_form {y : Fin 1 → VF M} {w : Fin r → RVInfinity M} (h : (y, w) ∈ X.carrier)
    (u : (hsObj g hT).object.domain) (hu : u.val = w) :
    gammaMapValue (hsObj g hT).form u = gammaMapValue g.form ⟨(y, w), h⟩ := by
  obtain ⟨e, he, -⟩ := exists_bundle_point (lab := lab) h
  let q : rvHeadStartBundle X k lab := ⟨_, he⟩
  have hq : u = pureRVTagQuotient _ q := Subtype.ext hu
  subst hq
  change gammaMapValue (contractedMeasuredRVObject (rvHeadStartBundle X k lab)
    (rvHeadStartBundle_tagged X k lab hT) (bundleGood g).pullback (bundleGood g).finite (bundleGood g).vfBounded
    (bundleGood g).form (bundleGood g).form_labels).form (pureRVTagQuotient _ q) = _
  rw [contractedMeasuredRVObject_form]
  change gammaMapValue g.form (headStartBaseProjection X k lab q) = _
  congr 1
  apply Subtype.ext
  rw [headStartBaseProjection_value]
  change (headStartBaseVF 1 k (Fin.append y e), w) = (y, w)
  rw [headStartBaseVF_append]

end DiamondIntegral.Section7.Lemma714Head

/-! ### Fibres of the pulled-back first-stage set -/

namespace DiamondIntegral.Section7.Lemma714Reduce
open DiamondIntegral.Section6 DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.Lemma714Frozen
open DiamondIntegral.Section7.Lemma714Head DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.BlowupCongruence
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.SpecialChains
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FiberwiseInput
open DiamondIntegral.Section7.FibreRestriction DiamondIntegral.Section7.KernelBaseChange
open DiamondIntegral.Section7.BaseExtension DiamondIntegral.Section7.FibreObjects DiamondIntegral.Section7.FibreComparison
open DiamondIntegral.Section7.FibreInvariance

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

section Ident
variable {T : LRV.Substructure M} {m r k : ℕ} {A : DefSet (rawMixedSpace (M := M) (m + 1 + 1) r) (T : Set M)}
  {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} (D : PrepContr (G := G) A ω)
  (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

include h00 hc hκ hs hv hsmall hΓ in
/-- **The fibre of the pulled-back first-stage set at a good point has the
head-start class of the slice contraction data.** -/
theorem cls_fibre_slice (hA : ProperInvariant (T : Set M) A.carrier) (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin (m + 1 + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (hNZ : ∀ p ∈ A.carrier, ∀ i, (p.2 (π i)).val ≠ iRVZero) (b₀ : Fin (m + 1) → VF M)
    (hgood : vfDim (rawRVSpace (M := M) 1) (sliceSet D.badA b₀ (hSb' b₀)) < 1 ∨
      (sliceSet D.badA b₀ (hSb' b₀)).carrier = ∅)
    (hU : (fibreObject T D.pullSet' D.ω₁ b₀ (restLabelsOrdered D.C (D.oldIndex ∘ π))
      (D.pull_fin h00 hc hκ hs hsmall π hFin b₀) (D.pull_nonzero π hNZ)).doublyBounded) :
    cls (objOf hc (adjoin T b₀) (fibreObject T D.pullSet' D.ω₁ b₀ (restLabelsOrdered D.C (D.oldIndex ∘ π))
        (D.pull_fin h00 hc hκ hs hsmall π hFin b₀) (D.pull_nonzero π hNZ)) hU) =
      castCls (show 1 + k = k + 1 by omega)
        (clsH hc ((D.sliceContr h00 hc hκ hs hv hsmall hΓ hA b₀ hgood).hgood hc h00 hκ hs
          (adjoin_small hκ hsmall b₀) π (fun x t => hFin (Fin.snoc b₀ (x 0)) t))) := by
  let C := D.sliceContr h00 hc hκ hs hv hsmall hΓ hA b₀ hgood
  let gH := C.hgood hc h00 hκ hs (adjoin_small hκ hsmall b₀) π (fun x t => hFin (Fin.snoc b₀ (x 0)) t)
  let U := fibreObject T D.pullSet' D.ω₁ b₀ (restLabelsOrdered D.C (D.oldIndex ∘ π))
    (D.pull_fin h00 hc hκ hs hsmall π hFin b₀) (D.pull_nonzero π hNZ)
  rw [clsH_eq_hsObj hc gH C.tagged]
  have hdom : ∀ u, u ∈ U.object.domain.carrier ↔ u ∈ (hsObj gH C.tagged).object.domain.carrier := by
    intro u
    rw [fibreObject_domain, hsObj_domain]
    constructor
    · rintro ⟨p, hp⟩
      have hpv : (D.psi p).val = (b₀, u) := hp
      rw [PrepContr.psi_val] at hpv
      obtain ⟨h1, h2⟩ := Prod.mk.inj hpv
      refine ⟨fun _ => (D.st.lift (D.prep p)).val.1 (Fin.last (m + 1)), p, ?_⟩
      change (D.g p).val = _
      rw [PrepContr.g_val, h1, h2]
    · rintro ⟨y, hy⟩
      obtain ⟨p₀, hb, -, hl⟩ := D.slice_lift b₀ ⟨(y, u), hy⟩
      refine ⟨p₀, ?_⟩
      change (D.psi p₀).val = _
      rw [PrepContr.psi_val, hb]
      exact Prod.ext rfl hl.symm
  refine cls_eq_of_volume hc (show k + 1 = 1 + k by omega) hU (hsObj_db gH C.tagged)
    (Map.inclusion (fun u hu => (hdom u).mp hu))
    ⟨fun u v h => Subtype.ext (by have h' := congrArg Subtype.val h; exact h'),
      fun v => ⟨⟨v.val, (hdom _).mpr v.property⟩, rfl⟩⟩ ?_ ?_
  · intro u
    obtain ⟨y, hy⟩ := (hsObj_domain gH C.tagged u.val).mp ((hdom _).mp u.property)
    obtain ⟨p₀, -, hx, hl⟩ := D.slice_lift b₀ ⟨(y, u.val), hy⟩
    have hlead := ((D.st.recover_target (D.st.lift (D.prep p₀)).val).mp (D.st.lift (D.prep p₀)).property).2
    rw [volumeGamma_eq, volumeGamma_eq, fibreObject_value,
      hsObj_value gH C.tagged hy (Map.inclusion (fun u hu => (hdom u).mp hu) u) rfl]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_add]
    simp only [Function.comp_apply, restLabelsOrdered, Fin.snoc_castSucc, Fin.snoc_last, Fin.append_left,
      Fin.append_right, Finset.univ_unique, Finset.prod_singleton]
    have hy0 : rv M (y 0) = u.val D.st.leading := by
      have hx' : y 0 = (D.st.lift (D.prep p₀)).val.1 (Fin.last (m + 1)) := hx
      have hl' : u.val = (D.st.lift (D.prep p₀)).val.2 := hl
      rw [hx', hlead, ← hl']
    rw [hy0, mul_comm]
    rfl
  · intro u
    obtain ⟨y, hy⟩ := (hsObj_domain gH C.tagged u.val).mp ((hdom _).mp u.property)
    rw [fibreObject_form, hsObj_form gH C.tagged hy (Map.inclusion (fun u hu => (hdom u).mp hu) u) rfl]
    change _ = gammaMapValue (sliceForm D.Xt D.formX b₀ (hSb' b₀)) ⟨(y, u.val), hy⟩
    rw [sliceForm_apply]
    change _ = gammaMapValue D.ω₁ (D.contrX ⟨(Fin.snoc b₀ (y 0), u.val), hy⟩)
    congr 1
    apply Subtype.ext
    rw [PrepContr.contrX_val]
    change ((b₀, u.val) : Mixed M (m + 1) D.st.arity) =
      (Fin.init (Fin.snoc (α := fun _ => VF M) b₀ (y 0)), u.val)
    rw [Fin.init_snoc]

include h00 hc hκ hs hv hsmall hΓ in
/-- **A named radius preserving the fibres and the form of the pulled-back
first-stage set.** -/
theorem pull_uniform :
    ∃ δ : Gamma M, (T : Set M).Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      (1 : Gamma M) ≤ δ ∧ ∀ (a a' : Fin (m + 1) → VF M), Congruent (fun _ => δ) a a' → ∀ u,
        ∀ ha : (a, u) ∈ D.pullSet'.carrier, ∃ ha' : (a', u) ∈ D.pullSet'.carrier,
          D.ω₁ ⟨(a', u), ha'⟩ = D.ω₁ ⟨(a, u), ha⟩ := by
  obtain ⟨δ, hδdef, hδ1, hU⟩ := firstSet_uniform h00 hc hv lin hκ hs hsmall hΓ D.C.data
  refine ⟨δ, hδdef, hδ1, fun a a' haa' u ha => ?_⟩
  let x : D.pullSet' := ⟨(a, u), ha⟩
  have hx := transl_value D.prep₁ D.prep₁_labels D.prep₁_transl x a ha
  have hxl : (D.prep₁ x).val.2 = u := D.prep₁_labels x
  have hmem : (a + trAt D.prep₁ x, u) ∈ D.st.contracted.carrier := by
    have := (D.prep₁ x).property
    have e : (D.prep₁ x).val = (a + trAt D.prep₁ x, u) := by
      have := hx
      rw [hxl] at this
      exact this
    rw [e] at this
    exact this
  have hcong : Congruent (fun _ => δ) (a + trAt D.prep₁ x) (a' + trAt D.prep₁ x) := by
    intro i
    have := haa' i
    simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using this
  obtain ⟨hb, hform⟩ := hU _ _ hcong u hmem
  obtain ⟨x', hx'⟩ := D.prep₁_bijective.2 ⟨_, hb⟩
  have hx'l : x'.val.2 = u := by
    have := D.prep₁_labels x'
    rw [hx'] at this
    exact this.symm
  have htr : trAt D.prep₁ x' = trAt D.prep₁ x := D.prep₁_transl x' x hx'l
  have hx'1 : x'.val.1 = a' := by
    funext i
    have h1 : (D.prep₁ x').val.1 i = x'.val.1 i + trAt D.prep₁ x' i := by
      change (D.prep₁ x').val.1 i = x'.val.1 i + ((D.prep₁ x').val.1 i - x'.val.1 i)
      abel
    rw [hx', htr] at h1
    have h2 : a' i + trAt D.prep₁ x i = x'.val.1 i + trAt D.prep₁ x i := h1
    exact (add_right_cancel h2).symm
  have hx'v : x'.val = (a', u) := Prod.ext hx'1 hx'l
  have ha' : (a', u) ∈ D.pullSet'.carrier := by
    rw [← hx'v]
    exact x'.property
  refine ⟨ha', ?_⟩
  have hxe : (⟨(a', u), ha'⟩ : D.pullSet') = x' := Subtype.ext hx'v.symm
  change restForm D.C.data (D.prep₁ ⟨(a', u), ha'⟩) = restForm D.C.data (D.prep₁ x)
  rw [hxe, hx']
  have hxe2 : D.prep₁ x = ⟨(a + trAt D.prep₁ x, u), hmem⟩ := by
    apply Subtype.ext
    have := hx
    rw [hxl] at this
    exact this
  rw [hxe2]
  exact hform

end Ident

end DiamondIntegral.Section7.Lemma714Reduce
