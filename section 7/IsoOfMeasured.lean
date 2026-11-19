import «section 7».ChartOfMeasured
import «section 6».MeasuredRVRestrictionBounds

/-! From Section 6's measured RV isomorphisms back to Section 4's chart
isomorphisms.

A map between Section 6 RV label sets over `S` has a raw graph definable over
`⟨S, ∅⟩` (`rawFun_graph`). Consequently a measured RV isomorphism between the
measured objects of two charts is a chart isomorphism (`isoOfMeasured`): the
label map is a definable bijection of the domains, and the balance identity
is the equality of corrected weights (`MeasuredRVBridge.totalWeight_eq`).
Together with `MeasuredRVBridge.measuredIso` this identifies the two notions,
and with `ChartOfMeasured.chartOf` Section 6's measured RV objects up to
isomorphism with Section 7's classes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.IsoOfMeasured
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts DiamondIntegral.Section4.FiniteTupleBlocks
open DiamondIntegral.Section6
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.RealBase
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.BoundedClasses

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}

section RawFun
variable {n m : ℕ} {A : DefSet (rawRVSpace (M := M) n) S} {B : DefSet (rawRVSpace (M := M) m) S}

/-- The raw values of a map of RV label sets. -/
def rawFun (f : Map A B) (w : Fin n → M) : Fin m → M :=
  if hw : w ∈ rvValues '' A.carrier then rvValues (f ⟨hw.choose, hw.choose_spec.1⟩).val else fun _ => iRVOne

omit hM in
theorem rawFun_of (f : Map A B) (a : A) : rawFun f (rvValues a.val) = rvValues (f a).val := by
  have hw : rvValues a.val ∈ rvValues '' A.carrier := ⟨a.val, a.property, rfl⟩
  rw [rawFun, dif_pos hw]
  have he : (⟨hw.choose, hw.choose_spec.1⟩ : A) = a := Subtype.ext (rvValues_injective hw.choose_spec.2)
  rw [he]

include hc in
theorem rawFun_graph (f : Map A B) :
    DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin (m + n) => .rv)
      (graphOn (rvValues '' A.carrier) (rawFun f)) := by
  let ρ : Fin n ⊕ Fin m → Fin (m + n) := Sum.elim (headIndex m n) (tailIndex m n)
  have hpre : S.Definable LRV ((fun w : Fin (m + n) → M => w ∘ ρ) ⁻¹'
      ((rawRVSpace (M := M) n).relation (rawRVSpace (M := M) m)
        (fun x y => ∃ a : A, a.val = x ∧ (f a).val = y))) :=
    f.graph_definable.preimage_comp ρ
  have hhead : ∀ w : Fin (m + n) → M, (w ∘ ρ) ∘ Sum.inl = w ∘ headIndex m n := fun _ => rfl
  have htail : ∀ w : Fin (m + n) → M, (w ∘ ρ) ∘ Sum.inr = w ∘ tailIndex m n := fun _ => rfl
  have he : graphOn (rvValues '' A.carrier) (rawFun f) = (fun w : Fin (m + n) → M => w ∘ ρ) ⁻¹'
      ((rawRVSpace (M := M) n).relation (rawRVSpace (M := M) m)
        (fun x y => ∃ a : A, a.val = x ∧ (f a).val = y)) := by
    ext w
    constructor
    · rintro ⟨hd, hv⟩
      obtain ⟨t, ht, hw⟩ := hd
      let a : A := ⟨t, ht⟩
      have hval : w ∘ tailIndex m n = rvValues (f a).val := by
        rw [← hv, ← hw]
        exact rawFun_of f a
      have hx : (w ∘ ρ) ∘ Sum.inl ∈ (rawRVSpace (M := M) n).domain := by
        rw [hhead, ← hw]
        exact ⟨t, rfl⟩
      have hy : (w ∘ ρ) ∘ Sum.inr ∈ (rawRVSpace (M := M) m).domain := by
        rw [htail, hval]
        exact ⟨_, rfl⟩
      refine ⟨hx, hy, a, ?_, ?_⟩
      · apply rvValues_injective
        rw [decode_rv]
        change rvValues t = (w ∘ ρ) ∘ Sum.inl
        rw [hhead, hw]
      · apply rvValues_injective
        rw [decode_rv]
        change rvValues (f a).val = (w ∘ ρ) ∘ Sum.inr
        rw [htail, hval]
    · rintro ⟨hx, hy, a, ha, hb⟩
      have h1 : w ∘ headIndex m n = rvValues a.val := by
        rw [ha, decode_rv]
        rfl
      have h2 : w ∘ tailIndex m n = rvValues (f a).val := by
        rw [hb, decode_rv]
        rfl
      refine ⟨?_, ?_⟩
      · rw [h1]
        exact ⟨a.val, a.property, rfl⟩
      · rw [h1, h2]
        exact rawFun_of f a
  rw [he]
  refine real_base hc hpre ?_
  intro w hw i
  rcases StrictCharts.block_cases m n i with ⟨i', rfl⟩ | ⟨i', rfl⟩
  · obtain ⟨hx, _, _⟩ := hw
    obtain ⟨t, ht⟩ := hx
    have := congrFun ht i'
    change (t i').val = w (headIndex m n i') at this
    rw [← this]
    exact (t i').property
  · obtain ⟨_, hy, _⟩ := hw
    obtain ⟨t, ht⟩ := hy
    have := congrFun ht i'
    change (t i').val = w (tailIndex m n i') at this
    rw [← this]
    exact (t i').property

end RawFun

theorem rvValues_image_rawDefSet {n : ℕ} (I : Set (Fin n → M))
    (hI : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin n => .rv) I) :
    rvValues '' (rawDefSet hc I hI).carrier = I := by
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hw
    refine ⟨rvTuple w (hI.proper w hw), ?_, rvValues_rvTuple _ _⟩
    show rvValues (rvTuple w (hI.proper w hw)) ∈ I
    rw [rvValues_rvTuple]
    exact hw

variable {k : ℕ}

/-- A measured RV isomorphism of the measured objects of two charts is a chart
isomorphism. -/
def isoOfMeasured {c d : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k}
    (e : MeasuredRVIso (toMeasured hc c) (toMeasured hc d)) : Iso c d := by
  have hdom : rvValues '' (toMeasured hc c).object.domain.carrier = c.domain :=
    rvValues_image_rawDefSet hc c.domain c.domain_definable
  have hdom' : rvValues '' (toMeasured hc d).object.domain.carrier = d.domain :=
    rvValues_image_rawDefSet hc d.domain d.domain_definable
  have hbij := rvIso_map_bijective e.iso
  refine isoOfMap c d (rawFun e.iso.hom.map) (hdom ▸ rawFun_graph hc e.iso.hom.map) ?_ ?_
  · refine ⟨?_, ?_, ?_⟩
    · intro w hw
      rw [← hdom] at hw
      obtain ⟨a, ha, rfl⟩ := hw
      rw [rawFun_of e.iso.hom.map ⟨a, ha⟩]
      exact (e.iso.hom.map ⟨a, ha⟩).property
    · intro w hw w' hw' he
      rw [← hdom] at hw hw'
      obtain ⟨a, ha, rfl⟩ := hw
      obtain ⟨a', ha', rfl⟩ := hw'
      rw [rawFun_of e.iso.hom.map ⟨a, ha⟩, rawFun_of e.iso.hom.map ⟨a', ha'⟩] at he
      have h := hbij.1 (Subtype.ext (rvValues_injective he))
      exact congrArg (fun x : (toMeasured hc c).object.domain => rvValues x.val) h
    · intro v hv
      rw [← hdom'] at hv
      obtain ⟨b, hb, rfl⟩ := hv
      obtain ⟨a, ha⟩ := hbij.2 ⟨b, hb⟩
      refine ⟨rvValues a.val, ?_, ?_⟩
      · rw [← hdom]
        exact ⟨a.val, a.property, rfl⟩
      · rw [rawFun_of e.iso.hom.map a, ha]
  · intro w hw
    rw [← hdom] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    have hb := e.balance ⟨a, ha⟩
    rw [totalWeight_eq, totalWeight_eq] at hb
    rw [rawFun_of e.iso.hom.map ⟨a, ha⟩]
    exact hb

/-- Charts have the same class exactly when their measured objects are
isomorphic in `μRV^db`. -/
theorem cls_eq_iff_measured {a b : Obj (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k} :
    cls a = cls b ↔ Nonempty (MeasuredRVIso (toMeasured hc a.toChart) (toMeasured hc b.toChart)) := by
  rw [cls_eq_iff]
  exact ⟨fun ⟨F⟩ => ⟨measuredIso hc F⟩, fun ⟨e⟩ => ⟨isoOfMeasured hc e⟩⟩

end DiamondIntegral.Section7.IsoOfMeasured
