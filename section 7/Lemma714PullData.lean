import «section 7».Lemma714Pipe
import «section 7».Lemma714Comps

/-! Lemma 7.14, part 25: witness data over the prepared base.

The freezing step evaluates the witness sets at the VF points of the prepared
base `B₀ ⊆ VF × RV^s`. For a map `ψ : B₀ → P` (the inverse of the base
preparation) and a set `D ⊆ M^(1+n)` of tuples `(z, v)`, the pulled-back
relation `pullSet ψ D ⊆ VF × RV^(s+n)` has, at `b ∈ B₀`, the row of `D` at the
parameter `ψ(b)` (`pull_row`). It is definable (`pullCarrier_definable`).

The file also gives the two raw projections used for keys: the RV labels of a
unary set (`rvPart`) and the swapped tuples `(labels, VF point)` (`rvvfPart`),
and the code map `(b, (a, u)) ↦ (a, u_RV)` that combines the VF point of one map
with the labels of another (`assembleVR`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Prod
open DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {s : ℕ}

/-! ### Splitting a point of `VF × RV^(s+n)` -/

/-- The base part `(a, w)` of `(a, w ++ t)`. -/
def headPart {n : ℕ} (y : Mixed M 1 (s + n)) : Mixed M 1 s := (y.1, fun j => y.2 (Fin.castAdd n j))

/-- The data part `t` of `(a, w ++ t)`. -/
def tailPart {n : ℕ} (y : Mixed M 1 (s + n)) : Fin n → RVInfinity M := fun j => y.2 (Fin.natAdd s j)

omit hM in
theorem headPart_append {n : ℕ} (b : Mixed M 1 s) (t : Fin n → RVInfinity M) :
    headPart ((b.1, Fin.append b.2 t) : Mixed M 1 (s + n)) = b :=
  Prod.ext rfl (funext fun j => Fin.append_left _ _ j)

omit hM in
theorem tailPart_append {n : ℕ} (b : Mixed M 1 s) (t : Fin n → RVInfinity M) :
    tailPart ((b.1, Fin.append b.2 t) : Mixed M 1 (s + n)) = t :=
  funext fun j => Fin.append_right _ _ j

/-! ### The pulled-back relation -/

section Pull
variable {B₀ : DefSet (rawMixedSpace (M := M) 1 s) S} {P : DefSet (rawMixedSpace (M := M) 1 0) S}
  (ψ : Map B₀ P)

/-- The relation `{(b, t) | b ∈ B₀, (ψ(b), t) ∈ D}`. -/
def pullCarrier {n : ℕ} (D : Set (Fin (1 + n) → M)) : Set (Mixed M 1 (s + n)) :=
  {y | ∃ h : headPart y ∈ B₀.carrier, Fin.append (vfValues (ψ ⟨headPart y, h⟩).val.1) (rvValues (tailPart y)) ∈ D}

theorem mem_pull_append {n : ℕ} (D : Set (Fin (1 + n) → M)) (b : Mixed M 1 s) (hb : b ∈ B₀.carrier)
    (t : Fin n → RVInfinity M) :
    ((b.1, Fin.append b.2 t) : Mixed M 1 (s + n)) ∈ pullCarrier ψ D ↔
      Fin.append (vfValues (ψ ⟨b, hb⟩).val.1) (rvValues t) ∈ D := by
  have e := headPart_append b t
  have e2 := tailPart_append b t
  constructor
  · rintro ⟨h, hy⟩
    have h3 : (⟨headPart ((b.1, Fin.append b.2 t) : Mixed M 1 (s + n)), h⟩ : B₀) = ⟨b, hb⟩ := Subtype.ext e
    rw [h3, e2] at hy
    exact hy
  · intro hy
    have hb' : headPart ((b.1, Fin.append b.2 t) : Mixed M 1 (s + n)) ∈ B₀.carrier := by rw [e]; exact hb
    refine ⟨hb', ?_⟩
    have h3 : (⟨headPart ((b.1, Fin.append b.2 t) : Mixed M 1 (s + n)), hb'⟩ : B₀) = ⟨b, hb⟩ := Subtype.ext e
    rw [h3, e2]
    exact hy

/-- Index of the graph of `ψ` in the layout `(y, z)`. -/
def graphIdx (s n : ℕ) : (Fin 1 ⊕ Fin s) ⊕ (Fin 1 ⊕ Fin 0) → Fin (1 + (s + n)) ⊕ Fin 1 :=
  Sum.elim (Sum.elim (fun _ => Sum.inl (Fin.castAdd (s + n) 0)) (fun j => Sum.inl (Fin.natAdd 1 (Fin.castAdd n j))))
    (Sum.elim (fun i => Sum.inr i) Fin.elim0)

/-- Index of the data tuple `(z, t)` in the layout `(y, z)`. -/
def dataIdx (s n : ℕ) : Fin (1 + n) → Fin (1 + (s + n)) ⊕ Fin 1 :=
  Fin.append (fun i => Sum.inr i) (fun j => Sum.inl (Fin.natAdd 1 (Fin.natAdd s j)))

omit hM in
theorem graph_codes_inl {n : ℕ} (y : Mixed M 1 (s + n)) (z : Fin 1 → M) (i : Fin 1 ⊕ Fin s) :
    (Sum.elim (mixedTuple y) z ∘ graphIdx s n) (Sum.inl i) = mixedValues (headPart y) i := by
  rcases i with i | i
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [graphIdx, mixedTuple, mixedValues, headPart]
  · simp [graphIdx, mixedTuple, mixedValues, headPart, rvValues]

omit hM in
theorem graph_codes {n : ℕ} (y : Mixed M 1 (s + n)) (z : Mixed M 1 0) :
    Sum.elim (mixedTuple y) (vfValues z.1) ∘ graphIdx s n = Sum.elim (mixedValues (headPart y)) (mixedValues z) := by
  funext i
  rcases i with (i | i) | (i | i)
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [graphIdx, mixedTuple, mixedValues, headPart]
  · simp [graphIdx, mixedTuple, mixedValues, headPart, rvValues]
  · simp [graphIdx, mixedValues]
  · exact i.elim0

omit hM in
theorem data_codes {n : ℕ} (y : Mixed M 1 (s + n)) (z : Fin 1 → M) :
    Sum.elim (mixedTuple y) z ∘ dataIdx s n = Fin.append z (rvValues (tailPart y)) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · simp [dataIdx]
  · simp [dataIdx, mixedTuple, tailPart, rvValues]

/-- **The pulled-back relation is definable.** -/
theorem pullCarrier_definable {n : ℕ} {D : Set (Fin (1 + n) → M)} (hD : S.Definable LRV D) :
    (rawMixedSpace (M := M) 1 (s + n)).Definable S (pullCarrier ψ D) := by
  rw [← mixedTuple_image_definable_iff]
  have hU : S.Definable LRV
      ((fun g : Fin (1 + (s + n)) ⊕ Fin 1 → M => g ∘ Sum.inl) ⁻¹'
          (mixedTuple '' (DefSet.univ (rawMixedSpace (M := M) 1 (s + n)) S).carrier) ∩
        ((fun g : Fin (1 + (s + n)) ⊕ Fin 1 → M => g ∘ graphIdx s n) ⁻¹' rawMixedMapGraph ψ ∩
          (fun g : Fin (1 + (s + n)) ⊕ Fin 1 → M => g ∘ dataIdx s n) ⁻¹' D)) :=
    (((mixedTuple_image_definable_iff _).mpr (DefSet.univ (rawMixedSpace (M := M) 1 (s + n)) S).definable).preimage_comp
      Sum.inl).inter (((show S.Definable LRV (rawMixedMapGraph ψ) from ψ.graph_definable).preimage_comp
        (graphIdx s n)).inter (hD.preimage_comp (dataIdx s n)))
  convert hU.image_comp (Sum.inl : Fin (1 + (s + n)) → Fin (1 + (s + n)) ⊕ Fin 1) using 1
  ext w
  constructor
  · rintro ⟨y, ⟨h, hy⟩, rfl⟩
    refine ⟨Sum.elim (mixedTuple y) (vfValues (ψ ⟨headPart y, h⟩).val.1), ⟨⟨y, trivial, rfl⟩, ?_, ?_⟩, rfl⟩
    · change Sum.elim (mixedTuple y) (vfValues (ψ ⟨headPart y, h⟩).val.1) ∘ graphIdx s n ∈ rawMixedMapGraph ψ
      rw [graph_codes]
      exact (rawMixedMapGraph_at ψ (headPart y) (ψ ⟨headPart y, h⟩).val).mpr ⟨⟨_, h⟩, rfl, rfl⟩
    · change Sum.elim (mixedTuple y) (vfValues (ψ ⟨headPart y, h⟩).val.1) ∘ dataIdx s n ∈ D
      rw [data_codes]
      exact hy
  · rintro ⟨g, ⟨⟨y, -, hy⟩, hG, hD'⟩, rfl⟩
    have hg : g = Sum.elim (mixedTuple y) (g ∘ Sum.inr) := by
      funext i
      rcases i with i | i
      · exact (congrFun hy i).symm
      · rfl
    refine ⟨y, ?_, hy⟩
    change g ∘ graphIdx s n ∈ rawMixedMapGraph ψ at hG
    change g ∘ dataIdx s n ∈ D at hD'
    obtain ⟨p, hp⟩ := (rawMixedMapGraph_iff ψ _).mp hG
    have hpv : p.val = headPart y := by
      apply mixedValues_injective
      funext i
      have h1 := congrFun hp (.inl i)
      rw [hg] at h1
      exact h1.trans (graph_codes_inl y _ i)
    have hz : g ∘ Sum.inr = vfValues (ψ p).val.1 := by
      funext i
      exact (congrFun hp (.inr (.inl i))).symm
    have hmem : headPart y ∈ B₀.carrier := by rw [← hpv]; exact p.property
    refine ⟨hmem, ?_⟩
    have hpe : p = ⟨headPart y, hmem⟩ := Subtype.ext hpv
    rw [hg, data_codes, hz] at hD'
    rw [← hpe]
    exact hD'

/-- The pulled-back relation, as a definable set. -/
def pullSet {n : ℕ} (D : Set (Fin (1 + n) → M)) (hD : S.Definable LRV D) :
    DefSet (rawMixedSpace (M := M) 1 (s + n)) S :=
  ⟨pullCarrier ψ D, pullCarrier_definable ψ hD⟩

/-- **The row of the pulled-back relation at `b` is the row of `D` at `ψ(b)`.** -/
theorem pull_row {n : ℕ} (D : Set (Fin (1 + n) → M)) (hD : S.Definable LRV D) (b : Mixed M 1 s)
    (hb : b ∈ B₀.carrier) :
    unaryRVDataRow (pullSet ψ D hD) b = {t | Fin.append (vfValues (ψ ⟨b, hb⟩).val.1) (rvValues t) ∈ D} := by
  ext t
  exact mem_pull_append ψ D b hb t

end Pull

/-! ### Raw projections of unary sets -/

section Raw
variable {q : ℕ}

/-- The RV labels of a unary set, as raw tuples. -/
def rvPart (X : Set (Mixed M 1 q)) : Set (Fin q → M) := {x | ∃ p ∈ X, rvValues p.2 = x}

theorem rvPart_definable (X : DefSet (rawMixedSpace (M := M) 1 q) S) : S.Definable LRV (rvPart X.carrier) := by
  have h := ((mixedTuple_image_definable_iff X.carrier).mpr X.definable).image_comp (Fin.natAdd 1 : Fin q → Fin (1 + q))
  convert h using 1
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨mixedTuple p, ⟨p, hp, rfl⟩, funext fun i => by simp [mixedTuple]⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, funext fun i => by simp [mixedTuple]⟩

/-- The tuples `(labels, VF point)` of a unary set. -/
def rvvfPart (X : Set (Mixed M 1 q)) : Set (Fin (q + 1) → M) :=
  {w | ∃ p ∈ X, Fin.append (rvValues p.2) (vfValues p.1) = w}

/-- The swap of the two blocks. -/
def swapIdx (q : ℕ) : Fin (q + 1) → Fin (1 + q) := Fin.append (Fin.natAdd 1) (Fin.castAdd q)

theorem rvvfPart_definable (X : DefSet (rawMixedSpace (M := M) 1 q) S) : S.Definable LRV (rvvfPart X.carrier) := by
  have h := ((mixedTuple_image_definable_iff X.carrier).mpr X.definable).image_comp (swapIdx q)
  convert h using 1
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨mixedTuple p, ⟨p, hp, rfl⟩, funext fun i => ?_⟩
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [mixedTuple, swapIdx]
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨p, hp, funext fun i => ?_⟩
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [mixedTuple, swapIdx]

end Raw

/-! ### Combining a VF point with labels -/

section AssembleVR
variable {q : ℕ}

/-- `((b, u), (a, e)) ↦ (a, u)`. -/
def vrPoint (x : Mixed M 1 q × Mixed M 1 0) : Mixed M 1 q := (x.2.1, x.1.2)

def vrCodes (z : (Fin 1 ⊕ Fin q) ⊕ (Fin 1 ⊕ Fin 0) → M) : Fin 1 ⊕ Fin q → M :=
  Sum.elim (fun i => z (.inr (.inl i))) (fun j => z (.inl (.inr j)))

omit hM in
theorem mixedValues_vr (x : Mixed M 1 q × Mixed M 1 0) :
    mixedValues (vrPoint x) = vrCodes (Sum.elim (mixedValues x.1) (mixedValues x.2)) := by
  funext i
  rcases i with i | i <;> rfl

/-- The code map `((b, u), (a, e)) ↦ (a, u)`. -/
def assembleVR (C : DefSet ((rawMixedSpace (M := M) 1 q).prod (rawMixedSpace (M := M) 1 0)) S) :
    Map C (DefSet.univ (rawMixedSpace (M := M) 1 q) S) := by
  have hc : ∀ c : ((rawMixedSpace (M := M) 1 q).prod (rawMixedSpace (M := M) 1 0)).domain,
      (vrCodes c.val : Fin 1 ⊕ Fin q → M) =
        mixedValues (vrPoint (((rawMixedSpace (M := M) 1 q).prod (rawMixedSpace (M := M) 1 0)).decode c)) := by
    intro c
    rw [mixedValues_vr]
    apply congrArg vrCodes
    funext i
    rcases i with i | i
    · exact (congrFun (mixedValues_decode (⟨c.val ∘ Sum.inl, c.property.1⟩ : (rawMixedSpace (M := M) 1 q).domain)) i).symm
    · exact (congrFun (mixedValues_decode (⟨c.val ∘ Sum.inr, c.property.2⟩ : (rawMixedSpace (M := M) 1 0).domain)) i).symm
  refine Map.ofCodes C vrPoint vrCodes ?_ ?_ ?_
  · rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  · intro c
    rw [hc c]
    exact mixedValues_mem_domain _
  · intro c
    apply mixedValues_injective
    exact (mixedValues_decode _).trans (hc c)

@[simp] theorem assembleVR_apply (C : DefSet ((rawMixedSpace (M := M) 1 q).prod (rawMixedSpace (M := M) 1 0)) S)
    (x : C) : (assembleVR C x).val = vrPoint x.val := rfl

end AssembleVR

end DiamondIntegral.Section7.Lemma714Prod
