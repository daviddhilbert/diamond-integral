import «section 8».TruncAmbient

/-! Images of concrete points under definable maps between sets of different dimensions.

`TruncAmbient` treats maps `A → B` with `A ⊆ VF^n × RV^l` and `B ⊆ VF^n × RV^{l'}`. The same
arguments apply when `B ⊆ VF^{n'} × RV^{l'}`:

* `exists_concrete_imageG`: the image of a concrete point is concrete (elementarity of `ℂ((t^{1/∞}))`
  in the ambient model, `TraceProjection.trace_exists`);
* `concrete_image_rationalG`: it is `m`-rational if the source point is (Galois invariance of
  definable sets);
* `invMapG`: the inverse of a bijective definable map is definable. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry SpecialTransformations.Section9
open DiamondIntegral.Section2 DiamondIntegral.Section3
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.GammaCells
open DiamondIntegral.Section8.Galois

local instance ambientGenStructure : LRV.Structure Carrier := canonicalInterpret
local instance ambientGenModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable (P : PuiseuxAmbient) {n l n' l' : ℕ}
  {A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)}
  {B : DefSet (rawMixedSpace (M := P.N) n' l') (P.G.real : Set P.N)}

/-- The reindexing of a pair of mixed code tuples. -/
def pairIdxG (n l n' l' : ℕ) : (Fin n ⊕ Fin l) ⊕ (Fin n' ⊕ Fin l') → Fin ((n + l) + (n' + l')) :=
  fun s => finSumFinEquiv (Sum.map finSumFinEquiv finSumFinEquiv s)

theorem append_comp_pairIdxG {K : Type} (u : Fin (n + l) → K) (v : Fin (n' + l') → K) :
    Fin.append u v ∘ pairIdxG n l n' l' = Sum.elim (u ∘ finSumFinEquiv) (v ∘ finSumFinEquiv) := by
  funext s
  cases s with
  | inl a => simp [pairIdxG, Fin.append_left]
  | inr b => simp [pairIdxG, Fin.append_right]

/-- The graph of `f` as a set of raw tuples. -/
def graphRawG (f : Map A B) : Set (Fin ((n + l) + (n' + l')) → P.N) :=
  {w | w ∘ pairIdxG n l n' l' ∈ (rawMixedSpace (M := P.N) n l).relation (rawMixedSpace (M := P.N) n' l')
    (fun x y => ∃ a : A, a.val = x ∧ (f a).val = y)}

theorem graphRawG_definable (f : Map A B) :
    (Set.range (P.e ∘ laurentCoefficientEnumeration)).Definable LRV (graphRawG P f) := by
  have h := f.graph_definable.preimage_comp (pairIdxG n l n' l')
  have hB : ((P.G.real : Set P.N)) = Set.range (P.e ∘ laurentCoefficientEnumeration) := P.hB
  exact hB ▸ h

theorem mem_relation_mixedG (R : Mixed P.N n l → Mixed P.N n' l' → Prop) (x : Mixed P.N n l)
    (y : Mixed P.N n' l') :
    (Sum.elim (mixedValues x) (mixedValues y) : (Fin n ⊕ Fin l) ⊕ (Fin n' ⊕ Fin l') → P.N) ∈
      (rawMixedSpace (M := P.N) n l).relation (rawMixedSpace (M := P.N) n' l') R ↔ R x y := by
  constructor
  · rintro ⟨hx, hy, h⟩
    have e1 : (rawMixedSpace (M := P.N) n l).decode ⟨_, hx⟩ = x := by
      have : (⟨Sum.elim (mixedValues x) (mixedValues y) ∘ Sum.inl, hx⟩ :
          (rawMixedSpace (M := P.N) n l).domain) = ⟨mixedValues x, mixedValues_mem_domain x⟩ := rfl
      rw [this, decode_mixedValues]
    have e2 : (rawMixedSpace (M := P.N) n' l').decode ⟨_, hy⟩ = y := by
      have : (⟨Sum.elim (mixedValues x) (mixedValues y) ∘ Sum.inr, hy⟩ :
          (rawMixedSpace (M := P.N) n' l').domain) = ⟨mixedValues y, mixedValues_mem_domain y⟩ := rfl
      rw [this, decode_mixedValues]
    rw [e1, e2] at h
    exact h
  · intro h
    refine ⟨mixedValues_mem_domain x, mixedValues_mem_domain y, ?_⟩
    have e1 : (rawMixedSpace (M := P.N) n l).decode ⟨mixedValues x, mixedValues_mem_domain x⟩ = x :=
      decode_mixedValues x
    have e2 : (rawMixedSpace (M := P.N) n' l').decode ⟨mixedValues y, mixedValues_mem_domain y⟩ = y :=
      decode_mixedValues y
    change R ((rawMixedSpace (M := P.N) n l).decode ⟨mixedValues x, mixedValues_mem_domain x⟩)
      ((rawMixedSpace (M := P.N) n' l').decode ⟨mixedValues y, mixedValues_mem_domain y⟩)
    rw [e1, e2]
    exact h

theorem mem_graphRawG_iff (f : Map A B) (p : (Fin n → Ser) × (Fin l → RV))
    (p' : (Fin n' → Ser) × (Fin l' → RV)) :
    Fin.append (P.e ∘ mixedRaw p) (P.e ∘ mixedRaw p') ∈ graphRawG P f ↔
      ∃ h : ePoint P p ∈ A.carrier, (f ⟨ePoint P p, h⟩).val = ePoint P p' := by
  change Fin.append (P.e ∘ mixedRaw p) (P.e ∘ mixedRaw p') ∘ pairIdxG n l n' l' ∈
    (rawMixedSpace (M := P.N) n l).relation (rawMixedSpace (M := P.N) n' l')
      (fun x y => ∃ a : A, a.val = x ∧ (f a).val = y) ↔ _
  rw [append_comp_pairIdxG]
  have h1 : (P.e ∘ mixedRaw p) ∘ finSumFinEquiv = mixedValues (ePoint P p) := (mixedValues_ePoint P p).symm
  have h2 : (P.e ∘ mixedRaw p') ∘ finSumFinEquiv = mixedValues (ePoint P p') := (mixedValues_ePoint P p').symm
  rw [h1, h2, mem_relation_mixedG]
  constructor
  · rintro ⟨a, ha, hfa⟩
    refine ⟨ha ▸ a.property, ?_⟩
    rw [← hfa]
    have : (⟨ePoint P p, ha ▸ a.property⟩ : A) = a := Subtype.ext ha.symm
    rw [this]
  · rintro ⟨h, hf⟩
    exact ⟨⟨ePoint P p, h⟩, rfl, hf⟩

/-- **The image of a concrete point is concrete**, in different dimensions. -/
theorem exists_concrete_imageG (f : Map A B) (p : (Fin n → Ser) × (Fin l → RV))
    (hp : ePoint P p ∈ A.carrier) :
    ∃ p' : (Fin n' → Ser) × (Fin l' → RV), (f ⟨ePoint P p, hp⟩).val = ePoint P p' := by
  have hex : ∃ y : Fin (n' + l') → P.N, Fin.append (P.e ∘ mixedRaw p) y ∈ graphRawG P f := by
    refine ⟨mixedValues (f ⟨ePoint P p, hp⟩).val ∘ finSumFinEquiv.symm, ?_⟩
    change Fin.append (P.e ∘ mixedRaw p) (mixedValues (f ⟨ePoint P p, hp⟩).val ∘ finSumFinEquiv.symm) ∘
      pairIdxG n l n' l' ∈ (rawMixedSpace (M := P.N) n l).relation (rawMixedSpace (M := P.N) n' l')
        (fun x y => ∃ a : A, a.val = x ∧ (f a).val = y)
    rw [append_comp_pairIdxG]
    have h1 : (P.e ∘ mixedRaw p) ∘ finSumFinEquiv = mixedValues (ePoint P p) := (mixedValues_ePoint P p).symm
    have h2 : (mixedValues (f ⟨ePoint P p, hp⟩).val ∘ finSumFinEquiv.symm) ∘ finSumFinEquiv =
        mixedValues (f ⟨ePoint P p, hp⟩).val := by
      funext s; simp
    rw [h1, h2, mem_relation_mixedG]
    exact ⟨⟨ePoint P p, hp⟩, rfl, rfl⟩
  obtain ⟨y', hy'⟩ := TraceProjection.trace_exists P.e laurentCoefficientEnumeration
    (graphRawG_definable P f) (mixedRaw p) hex
  have hdom : (P.e ∘ y') ∘ finSumFinEquiv ∈ (rawMixedSpace (M := P.N) n' l').domain := by
    obtain ⟨_, hy, _⟩ := hy'
    rw [append_comp_pairIdxG] at hy
    exact hy
  have hsort := e_sorted_of_mixed P hdom
  refine ⟨decodeRaw y', ?_⟩
  have hy'' : Fin.append (P.e ∘ mixedRaw p) (P.e ∘ mixedRaw (decodeRaw y')) ∈ graphRawG P f := by
    rw [mixedRaw_decodeRaw hsort]
    exact hy'
  obtain ⟨_, hf⟩ := (mem_graphRawG_iff P f p _).mp hy''
  exact hf

theorem graphTraceG_definable (f : Map A B) :
    {c | baseCarrier c}.Definable LRV {z : Fin ((n + l) + (n' + l')) → Carrier | P.e ∘ z ∈ graphRawG P f} := by
  have h := (elementaryActualDefinableEquiv P.e laurentCoefficientEnumeration
    (⟨graphRawG P f, graphRawG_definable P f⟩ : LRV.DefinableSet _ (Fin ((n + l) + (n' + l'))))).property
  have h' : (Set.range laurentCoefficientEnumeration).Definable LRV
      {z : Fin ((n + l) + (n' + l')) → Carrier | P.e ∘ z ∈ graphRawG P f} := h
  rw [laurentCoefficientEnumeration_range] at h'
  exact h'

/-- **Images of `m`-rational concrete points are `m`-rational**, in different dimensions. -/
theorem concrete_image_rationalG (f : Map A B) (m : ℕ+) (p : (Fin n → Ser) × (Fin l → RV))
    (hp : ePoint P p ∈ A.carrier) (p' : (Fin n' → Ser) × (Fin l' → RV))
    (hf : (f ⟨ePoint P p, hp⟩).val = ePoint P p') (hrat : RationalPoint m p) : RationalPoint m p' := by
  have hmem : Fin.append (mixedRaw p) (mixedRaw p') ∈
      {z : Fin ((n + l) + (n' + l')) → Carrier | P.e ∘ z ∈ graphRawG P f} := by
    change P.e ∘ Fin.append (mixedRaw p) (mixedRaw p') ∈ graphRawG P f
    have he : P.e ∘ Fin.append (mixedRaw p) (mixedRaw p') = Fin.append (P.e ∘ mixedRaw p) (P.e ∘ mixedRaw p') := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [Fin.append_left, Fin.append_right]
    rw [he]
    exact (mem_graphRawG_iff P f p p').mpr ⟨hp, hf⟩
  have hact := (raw_original_definable_invariant (levelRoots m) _ (graphTraceG_definable P f) _).mpr hmem
  have hcomp : carrierAction (levelRoots m) ∘ Fin.append (mixedRaw p) (mixedRaw p') =
      Fin.append (mixedRaw p) (mixedRaw (actPoint (levelRoots m) p')) := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [Function.comp_apply, Fin.append_left]
      have := congrFun (act_mixedRaw (levelRoots m) p) i
      rw [(actPoint_eq_iff m p).mpr hrat] at this
      exact this
    · simp only [Function.comp_apply, Fin.append_right]
      exact congrFun (act_mixedRaw (levelRoots m) p') j
  rw [hcomp] at hact
  change P.e ∘ Fin.append (mixedRaw p) (mixedRaw (actPoint (levelRoots m) p')) ∈ graphRawG P f at hact
  have he : P.e ∘ Fin.append (mixedRaw p) (mixedRaw (actPoint (levelRoots m) p')) =
      Fin.append (P.e ∘ mixedRaw p) (P.e ∘ mixedRaw (actPoint (levelRoots m) p')) := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [Fin.append_left, Fin.append_right]
  rw [he] at hact
  obtain ⟨_, hf'⟩ := (mem_graphRawG_iff P f p _).mp hact
  have hfix : actPoint (levelRoots m) p' = p' := ePoint_injective P (hf'.symm.trans hf)
  exact (actPoint_eq_iff m p').mp hfix

/-- The inverse of a bijective definable map, in different dimensions. -/
def invMapG (F : Map A B) (hF : Function.Bijective F) : Map B A where
  toFun := (Equiv.ofBijective F hF).symm
  graph_definable := by
    refine (F.graph_definable.swap _ _).congr _ _ fun y x => ?_
    constructor
    · rintro ⟨a, ha, hb⟩
      refine ⟨F a, hb, ?_⟩
      rw [← ha]
      exact congrArg Subtype.val ((Equiv.ofBijective F hF).symm_apply_apply a)
    · rintro ⟨c, hc, hx⟩
      refine ⟨(Equiv.ofBijective F hF).symm c, hx, ?_⟩
      rw [← hc]
      exact congrArg Subtype.val ((Equiv.ofBijective F hF).apply_symm_apply c)

theorem apply_invMapG (F : Map A B) (hF : Function.Bijective F) (c : B) : F (invMapG P F hF c) = c :=
  (Equiv.ofBijective F hF).apply_symm_apply c

end DiamondIntegral.Section8.Truncation
