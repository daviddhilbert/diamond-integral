import «section 7».Lemma714Transport

/-! Lemma 7.14, part 28: the chart of a head-start object.

For a head-start chain set `X` with labels `λ`, the chart of its head-start
object has as domain the raw labels of `X` (`hsObj_rawDom`); at the labels `w`
of `(y, w) ∈ X` its structural map is `(rv(y), w ∘ λ)` (`hsObj_rawCoord`), its
volume is the form at `(y, w)` (`hsObj_rawVol`), and its corrected weight is
`ω(y, w) · |rv(y)| · ∏ |w(λ i)|` (`hsObj_weight`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma714Head
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {T : LRV.Substructure M} {r k : ℕ} {X : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)} {lab : Fin k → Fin r}

/-- A point of the head-start bundle over a point of `X`. -/
theorem exists_bundle_point {y : Fin 1 → VF M} {w : Fin r → RVInfinity M} (h : (y, w) ∈ X.carrier) :
    ∃ e : Fin k → VF M, ((Fin.append y e, w) : Mixed M (1 + k) r) ∈ (rvHeadStartBundle X k lab).carrier ∧
      tupleRV M e = w ∘ lab := by
  obtain ⟨e, he⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) (w ∘ lab)
  refine ⟨e, (mem_rvHeadStartBundle X k lab _ w).mpr ⟨?_, ?_⟩, he⟩
  · rw [headStartBaseVF_append]
    exact h
  · rw [headStartExtraVF_append]
    exact he

variable (g : HGood X lab) (hT : ∀ p ∈ X.carrier, ∀ q ∈ X.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)

theorem hsObj_domain (w : Fin r → RVInfinity M) :
    w ∈ (hsObj g hT).object.domain.carrier ↔ ∃ y, (y, w) ∈ X.carrier := by
  change w ∈ Set.range (fun q : rvHeadStartBundle X k lab => (rvTailMap _ q).val) ↔ _
  constructor
  · rintro ⟨q, rfl⟩
    have hq := (mem_rvHeadStartBundle X k lab q.val.1 q.val.2).mp q.property
    exact ⟨_, hq.1⟩
  · rintro ⟨y, hy⟩
    obtain ⟨e, he, -⟩ := exists_bundle_point (lab := lab) hy
    exact ⟨⟨_, he⟩, rfl⟩

theorem hsObj_rawDom : rawDom (hsObj g hT) = rvValues '' {w | ∃ y, (y, w) ∈ X.carrier} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, (hsObj_domain g hT w).mp hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, (hsObj_domain g hT w).mpr hw, rfl⟩

theorem hsObj_rawCoord {y : Fin 1 → VF M} {w : Fin r → RVInfinity M} (h : (y, w) ∈ X.carrier) :
    rawCoord (hsObj g hT) (rvValues w) = Fin.append (fun _ : Fin 1 => (rv M (y 0)).val) (fun i => (w (lab i)).val) := by
  obtain ⟨e, he, het⟩ := exists_bundle_point (lab := lab) h
  let q : rvHeadStartBundle X k lab := ⟨_, he⟩
  have h1 := rawCoord_of (hsObj g hT) (pureRVTagQuotient _ q)
  change rawCoord (hsObj g hT) (rvValues w) = rvValues ((preparedRVObject (rvHeadStartBundle X k lab) _).value
    (pureRVTagQuotient _ q)) at h1
  rw [h1, preparedRVObject_value]
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · have hl : l = 0 := Subsingleton.elim _ _
    subst hl
    simp only [Fin.append_left]
    change (rv M ((Fin.append y e : Fin (1 + k) → VF M) (Fin.castAdd k 0))).val = _
    rw [Fin.append_left]
  · simp only [Fin.append_right]
    change (rv M ((Fin.append y e : Fin (1 + k) → VF M) (Fin.natAdd 1 l))).val = _
    rw [Fin.append_right]
    exact congrArg Subtype.val (congrFun het l)

theorem hsObj_rawVol {y : Fin 1 → VF M} {w : Fin r → RVInfinity M} (h : (y, w) ∈ X.carrier) :
    rawVol (hsObj g hT) (rvValues w) = gammaMapValue g.form ⟨(y, w), h⟩ := by
  obtain ⟨e, he, -⟩ := exists_bundle_point (lab := lab) h
  let q : rvHeadStartBundle X k lab := ⟨_, he⟩
  have h1 := rawVol_of (hsObj g hT) (pureRVTagQuotient _ q)
  change rawVol (hsObj g hT) (rvValues w) = gammaMapValue (contractedMeasuredRVObject (rvHeadStartBundle X k lab)
    (rvHeadStartBundle_tagged X k lab hT) (bundleGood g).pullback (bundleGood g).finite (bundleGood g).vfBounded
    (bundleGood g).form (bundleGood g).form_labels).form (pureRVTagQuotient _ q) at h1
  rw [h1, contractedMeasuredRVObject_form]
  change gammaMapValue g.form (headStartBaseProjection X k lab q) = _
  congr 1
  apply Subtype.ext
  rw [headStartBaseProjection_value]
  change (headStartBaseVF 1 k (Fin.append y e), w) = (y, w)
  rw [headStartBaseVF_append]

theorem hsObj_weight (hc : CanonicalStructure.IsCanonical (M := M)) {y : Fin 1 → VF M} {w : Fin r → RVInfinity M}
    (h : (y, w) ∈ X.carrier) :
    (chartOf hc (hsObj g hT)).correctedWeight (rvValues w) =
      gammaMapValue g.form ⟨(y, w), h⟩ * (GammaParameters.codeValue (rv M (y 0)).val *
        ∏ i, GammaParameters.codeValue (w (lab i)).val) := by
  change rawVol (hsObj g hT) (rvValues w) * ∏ i, GammaParameters.codeValue (rawCoord (hsObj g hT) (rvValues w) i) = _
  rw [hsObj_rawVol g hT h, hsObj_rawCoord g hT h, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, Finset.univ_unique, Finset.prod_singleton]

end DiamondIntegral.Section7.Lemma714Head
