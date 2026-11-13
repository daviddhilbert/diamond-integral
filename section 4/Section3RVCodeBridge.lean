import «section 3».GammaGroundSyntaxBridge
import «section 3».GammaGroundSortedSyntax
import «section 3».GammaGroundRawGraphs
import «section 3».GammaGroundMapImages
import «section 3».GammaGroundRawDescent
import «section 3».GammaGroundBijections
import «section 3».GammaGroundMapRestrictions
import «section 4».RVRealProducts

/-! Exact original-base conversion between native Section 3 RV domains
and the raw RV tuple charts of Section 4. No parameter is added. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3RVCodeBridge
open FiniteTupleBlocks RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def rawDomain {n : ℕ} (D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) : Set (Fin n → M) :=
  rvValues '' D.carrier

theorem rawDomain_definable {n : ℕ} (D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    DefinableOverBase B (fun _ : Fin n => .rv) (rawDomain D) := D.definable.toRVBase

def rawEquiv {n : ℕ} (D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) : D ≃ rawDomain D :=
  Equiv.ofBijective (fun a => ⟨rvValues a.val, ⟨a.val, a.property, rfl⟩⟩) ⟨
    (fun a b h => Subtype.ext (rvValues_injective (congrArg Subtype.val h))), by
      rintro ⟨x, a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩⟩

theorem rawEquiv_apply {n : ℕ} (D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) (a : D) :
    (rawEquiv D a).val = rvValues a.val := rfl

theorem rawEquiv_symm_value {n : ℕ} (D : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (a : rawDomain D) : rvValues ((rawEquiv D).symm a).val = a.val :=
  congrArg Subtype.val ((rawEquiv D).apply_symm_apply a)

def ofRaw {n : ℕ} (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ : Fin n => .rv) A) :
    GammaGroundDefSet hc B (rawRVSpace (M := M) n) where
  carrier := {a | rvValues a ∈ A}
  definable := by
    apply gammaGroundDefinable_iff_rvBase.mpr
    have he : rvValues '' {a : Fin n → CanonicalRV.RVSort M | rvValues a ∈ A} = A := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hx
        exact ⟨fun i => ⟨x i, hA.proper x hx i⟩, hx, rfl⟩
    exact (congrArg (fun U : Set (Fin n → M) =>
      DefinableOverBase B (fun _ : Fin n => .rv) U) he).mpr hA

theorem rawDomain_ofRaw {n : ℕ} (A : Set (Fin n → M))
    (hA : DefinableOverBase B (fun _ : Fin n => .rv) A) : rawDomain (ofRaw (hc := hc) A hA) = A := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hx
    exact ⟨fun i => ⟨x i, hA.proper x hx i⟩, hx, rfl⟩

def joinedGraph {n k : ℕ} {D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    {E : GammaGroundDefSet hc B (rawRVSpace (M := M) k)} (f : GammaGroundMap D E) :
    Set (Fin (k + n) → M) :=
  {w | ∃ a : D, w = join k n (rvValues a.val) (rvValues (f a).val)}

theorem joinedGraph_definable {n k : ℕ}
    {D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    {E : GammaGroundDefSet hc B (rawRVSpace (M := M) k)} (f : GammaGroundMap D E) :
    DefinableOverBase B (fun _ : Fin (k + n) => .rv) (joinedGraph f) := by
  let π : Fin n ⊕ Fin k → Fin (k + n) := Sum.elim (headIndex k n) (tailIndex k n)
  have h := f.raw_graph_definable.preimage_comp π
  have he : {w | w ∘ π ∈ (rawRVSpace (M := M) n).relation (rawRVSpace k) f.graph} = joinedGraph f := by
    ext w
    constructor
    · rintro ⟨hu, hv, a, ha, hf⟩
      have hh : rvValues a.val = w ∘ headIndex k n := by
        rw [ha, rvValues_decode]
        rfl
      have ht : rvValues (f a).val = w ∘ tailIndex k n := by
        rw [hf, rvValues_decode]
        rfl
      exact ⟨a, (join_reconstruct k n w).symm.trans (by rw [← hh, ← ht])⟩
    · rintro ⟨a, rfl⟩
      have hh : (join k n (rvValues a.val) (rvValues (f a).val)) ∘ π ∘ Sum.inl = rvValues a.val := by
        funext i
        exact join_head k n _ _ i
      have ht : (join k n (rvValues a.val) (rvValues (f a).val)) ∘ π ∘ Sum.inr = rvValues (f a).val := by
        funext i
        exact join_tail k n _ _ i
      change ∃ hu, ∃ hv, ∃ b : D,
        b.val = (rawRVSpace n).decode ⟨_, hu⟩ ∧ (f b).val = (rawRVSpace k).decode ⟨_, hv⟩
      refine ⟨hh.symm ▸ Set.mem_range_self a.val, ht.symm ▸ Set.mem_range_self (f a).val, a, ?_, ?_⟩
      · apply rvValues_injective
        rw [rvValues_decode]
        exact hh.symm
      · apply rvValues_injective
        rw [rvValues_decode]
        exact ht.symm
  have hraw : GammaGroundRawDefinable hc B (joinedGraph f) := by
    exact h.congr (fun w => (Set.ext_iff.mp he w))
  apply (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) ?_).mp hraw
  rintro w ⟨a, rfl⟩
  apply GammaBoundedProducts.all_coordinates k n iRV
  · intro i
    rw [join_head]
    exact (a.val i).property
  · intro i
    rw [join_tail]
    exact ((f a).val i).property

def rawMap {n k : ℕ} {D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    {E : GammaGroundDefSet hc B (rawRVSpace (M := M) k)} (f : GammaGroundMap D E)
    (x : Fin n → M) : Fin k → M :=
  if hx : x ∈ rawDomain D then rvValues (f ((rawEquiv D).symm ⟨x, hx⟩)).val else fun _ => iRVZero

theorem rawMap_apply {n k : ℕ} {D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    {E : GammaGroundDefSet hc B (rawRVSpace (M := M) k)} (f : GammaGroundMap D E) (a : D) :
    rawMap f (rvValues a.val) = rvValues (f a).val := by
  have hx : rvValues a.val ∈ rawDomain D := ⟨a.val, a.property, rfl⟩
  simp only [rawMap, dif_pos hx]
  have he : (⟨rvValues a.val, hx⟩ : rawDomain D) = rawEquiv D a := rfl
  rw [he, Equiv.symm_apply_apply]

theorem joinedGraph_eq {n k : ℕ} {D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    {E : GammaGroundDefSet hc B (rawRVSpace (M := M) k)} (f : GammaGroundMap D E) :
    joinedGraph f = graphOn (rawDomain D) (rawMap f) := by
  ext w
  rw [RVRealProducts.graphOn_exists]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨rvValues a.val, ⟨a.val, a.property, rfl⟩, by rw [rawMap_apply]⟩
  · rintro ⟨x, hx, rfl⟩
    let a := (rawEquiv D).symm ⟨x, hx⟩
    have ha : rvValues a.val = x := rawEquiv_symm_value D ⟨x, hx⟩
    refine ⟨a, ?_⟩
    rw [← ha, rawMap_apply]

theorem rawMap_definable {n k : ℕ} {D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    {E : GammaGroundDefSet hc B (rawRVSpace (M := M) k)} (f : GammaGroundMap D E) :
    DefinableOverBase B (fun _ : Fin (k + n) => .rv) (graphOn (rawDomain D) (rawMap f)) :=
  joinedGraph_eq f ▸ joinedGraph_definable f

theorem rawMap_bijective {n k : ℕ} {D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    {E : GammaGroundDefSet hc B (rawRVSpace (M := M) k)} (f : GammaGroundMap D E)
    (hf : Function.Bijective f) : Set.BijOn (rawMap f) (rawDomain D) (rawDomain E) := by
  have image (x : Fin n → M) (hx : x ∈ rawDomain D) : rawMap f x ∈ rawDomain E := by
    let a := (rawEquiv D).symm ⟨x, hx⟩
    have ha : rvValues a.val = x := rawEquiv_symm_value D ⟨x, hx⟩
    rw [← ha, rawMap_apply]
    exact ⟨(f a).val, (f a).property, rfl⟩
  refine ⟨image, ?_, ?_⟩
  · intro x hx y hy hxy
    let a := (rawEquiv D).symm ⟨x, hx⟩
    let b := (rawEquiv D).symm ⟨y, hy⟩
    have ha : rvValues a.val = x := rawEquiv_symm_value D ⟨x, hx⟩
    have hb : rvValues b.val = y := rawEquiv_symm_value D ⟨y, hy⟩
    have he : f a = f b := by
      apply Subtype.ext
      apply rvValues_injective
      rw [← rawMap_apply, ← rawMap_apply, ha, hb]
      exact hxy
    exact ha.symm.trans ((congrArg (fun a : D => rvValues a.val) (hf.1 he)).trans hb)
  · intro y hy
    let b := (rawEquiv E).symm ⟨y, hy⟩
    obtain ⟨a, ha⟩ := hf.2 b
    refine ⟨rvValues a.val, ⟨a.val, a.property, rfl⟩, ?_⟩
    rw [rawMap_apply, ha]
    exact rawEquiv_symm_value E ⟨y, hy⟩

theorem rawMap_finite {n k : ℕ} {D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    {E : GammaGroundDefSet hc B (rawRVSpace (M := M) k)} (f : GammaGroundMap D E)
    (hf : f.FiniteFibres) (t : Fin k → M) :
    {x | x ∈ rawDomain D ∧ rawMap f x = t}.Finite := by
  by_cases h : {x | x ∈ rawDomain D ∧ rawMap f x = t}.Nonempty
  · obtain ⟨x, hx, hxt⟩ := h
    let a := (rawEquiv D).symm ⟨x, hx⟩
    have ha : rvValues a.val = x := rawEquiv_symm_value D ⟨x, hx⟩
    have hfin := (hf (f a)).image (fun b : D => rvValues b.val)
    apply hfin.subset
    rintro y ⟨hy, hyt⟩
    let b := (rawEquiv D).symm ⟨y, hy⟩
    have hb : rvValues b.val = y := rawEquiv_symm_value D ⟨y, hy⟩
    refine ⟨b, ?_, hb⟩
    apply Subtype.ext
    apply rvValues_injective
    rw [← rawMap_apply f b, ← rawMap_apply f a, hb, ha, hyt, hxt]
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact Set.finite_empty

def mapOfRaw {n k : ℕ} (A : Set (Fin n → M))
    (hA : DefinableOverBase B (fun _ : Fin n => .rv) A)
    (F : (Fin n → M) → (Fin k → M))
    (hF : DefinableOverBase B (fun _ : Fin (k + n) => .rv) (graphOn A F))
    (hp : ∀ x ∈ A, ∀ i, iRV (F x i)) :
    GammaGroundMap (ofRaw (hc := hc) A hA) (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) k)) where
  toFun a := ⟨fun i => ⟨F (rvValues a.val) i, hp _ a.property i⟩, Set.mem_univ _⟩
  graph_definable := by
    have hraw := ((gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B)
      (fun z hz i => hF.proper z hz i)).mpr hF).preimage_comp
        (join k n (Sum.inl : Fin n → Fin n ⊕ Fin k) Sum.inr)
    apply GammaGroundDefinable.of_real_codes
    change GammaGroundRawDefinable hc B (ι := Fin n ⊕ Fin k) _
    apply hraw.congr
    intro z
    let π : Fin (k + n) → Fin n ⊕ Fin k := join k n Sum.inl Sum.inr
    have hh : (z ∘ π) ∘ headIndex k n = z ∘ Sum.inl := by
      funext i
      exact congrArg z (join_head k n Sum.inl Sum.inr i)
    have ht : (z ∘ π) ∘ tailIndex k n = z ∘ Sum.inr := by
      funext i
      exact congrArg z (join_tail k n Sum.inl Sum.inr i)
    change ((z ∘ π) ∘ headIndex k n ∈ A ∧ F ((z ∘ π) ∘ headIndex k n) =
      (z ∘ π) ∘ tailIndex k n) ↔ _
    rw [hh, ht]
    constructor
    · rintro ⟨hz, he⟩
      have hu : z ∘ Sum.inl ∈ (rawRVSpace (M := M) n).domain :=
        ⟨fun i => ⟨z (.inl i), hA.proper _ hz i⟩, rfl⟩
      have hv : z ∘ Sum.inr ∈ (rawRVSpace (M := M) k).domain := by
        refine ⟨fun i => ⟨z (.inr i), ?_⟩, rfl⟩
        exact (congrArg iRV (congrFun he i)).mp (hp _ hz i)
      let a : ofRaw (hc := hc) A hA := ⟨(rawRVSpace n).decode ⟨z ∘ Sum.inl, hu⟩, by
        change rvValues ((rawRVSpace n).decode ⟨z ∘ Sum.inl, hu⟩) ∈ A
        rw [rvValues_decode]
        exact hz⟩
      refine ⟨⟨hu, hv⟩, a, rfl, ?_⟩
      apply rvValues_injective
      change F (rvValues a.val) = rvValues ((rawRVSpace k).decode ⟨z ∘ Sum.inr, hv⟩)
      simp only [a, rvValues_decode]
      exact he
    · rintro ⟨⟨hu, hv⟩, a, ha, hf⟩
      change a.val = (rawRVSpace n).decode ⟨z ∘ Sum.inl, hu⟩ at ha
      have hs : rvValues a.val = z ∘ Sum.inl := by rw [ha, rvValues_decode]
      have ht' : F (rvValues a.val) = z ∘ Sum.inr := by
        change (fun i => (⟨F (rvValues a.val) i, hp _ a.property i⟩ : CanonicalRV.RVSort M)) =
          (rawRVSpace k).decode ⟨z ∘ Sum.inr, hv⟩ at hf
        have he := congrArg rvValues hf
        exact he.trans (rvValues_decode ⟨z ∘ Sum.inr, hv⟩)
      exact ⟨hs ▸ a.property, (congrArg F hs).symm.trans ht'⟩

theorem mapOfRaw_value {n k : ℕ} (A : Set (Fin n → M))
    (hA : DefinableOverBase B (fun _ : Fin n => .rv) A)
    (F : (Fin n → M) → (Fin k → M))
    (hF : DefinableOverBase B (fun _ : Fin (k + n) => .rv) (graphOn A F))
    (hp : ∀ x ∈ A, ∀ i, iRV (F x i)) (a : ofRaw (hc := hc) A hA) :
    rvValues ((mapOfRaw A hA F hF hp) a).val = F (rvValues a.val) := rfl

def bijectionOfRaw {n k : ℕ} (A : Set (Fin n → M)) (E : Set (Fin k → M))
    (hA : DefinableOverBase B (fun _ : Fin n => .rv) A)
    (hE : DefinableOverBase B (fun _ : Fin k => .rv) E)
    (F : (Fin n → M) → (Fin k → M))
    (hF : DefinableOverBase B (fun _ : Fin (k + n) => .rv) (graphOn A F))
    (hbij : Set.BijOn F A E) : GammaGroundBijection (ofRaw (hc := hc) A hA) (ofRaw E hE) where
  map := (mapOfRaw A hA F hF (fun x hx i => hE.proper _ (hbij.mapsTo hx) i)).corestrict
    (fun a => hbij.mapsTo a.property)
  bijective := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply rvValues_injective
      apply hbij.injOn a.property b.property
      exact congrArg (fun v : ofRaw (hc := hc) E hE => rvValues v.val) hab
    · intro b
      obtain ⟨x, hx, hxb⟩ := hbij.surjOn b.property
      let a : ofRaw (hc := hc) A hA := ⟨fun i => ⟨x i, hA.proper _ hx i⟩, hx⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      apply rvValues_injective
      exact hxb

theorem bijectionOfRaw_value {n k : ℕ} (A : Set (Fin n → M)) (E : Set (Fin k → M))
    (hA : DefinableOverBase B (fun _ : Fin n => .rv) A)
    (hE : DefinableOverBase B (fun _ : Fin k => .rv) E)
    (F : (Fin n → M) → (Fin k → M))
    (hF : DefinableOverBase B (fun _ : Fin (k + n) => .rv) (graphOn A F))
    (hbij : Set.BijOn F A E) (a : ofRaw (hc := hc) A hA) :
    rvValues ((bijectionOfRaw A E hA hE F hF hbij).map a).val = F (rvValues a.val) := rfl

end DiamondIntegral.Section4.Section3RVCodeBridge
