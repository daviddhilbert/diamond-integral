import «section 8».TruncTransfer
import «section 8».TraceProjection
import «section 8».HmAnnularShell
import «section 8».GaloisLattice

/-! Concrete points and the ambient model.

* `lt_value_eVF_iff`: for a concrete series `y` and `β ∈ ℚ`, `π^β < v(e y)` in the ambient iff
  `β < ordS y`; so congruences of concrete points modulo `𝔪_β` are the same in both models.
* `fixed_iff_rational`, `labelFixed_iff`: a concrete series (an RV element) is fixed by the Galois
  action of `levelRoots m` iff it is `m`-rational.
* `exists_concrete_image`: for a map `f : A → B` between sets definable over the base of Section 8,
  the image of a concrete point is the image of a concrete point (elementarity); it is unique, and
  `m`-rational if the source point is (`concrete_image_rational`). -/

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

local instance ambientTruncStructure : LRV.Structure Carrier := canonicalInterpret
local instance ambientTruncModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable (P : PuiseuxAmbient) {n l : ℕ}

local notation "π" => uniformizerValue P

theorem eVF_eq (g : Ser) : eVF P g = ambientPuiseuxFieldHom P.e g := Subtype.ext rfl

theorem eVF_sub (x y : Ser) : eVF P (x - y) = eVF P x - eVF P y := by
  rw [eVF_eq, eVF_eq, eVF_eq, map_sub]

theorem eVF_injective : Function.Injective (eVF P) := by
  intro x y h
  have h1 := congrArg Subtype.val h
  exact Sum.inl_injective (P.e.injective h1)

theorem value_eVF (g : Ser) (hg : g ≠ 0) :
    Values.vfValueHom (eVF P g) = (qpow π ((g : HahnSeries ℚ ℂ).order)).val := by
  have hne : Values.vfValueHom (eVF P g) ≠ Values.infinity := by
    rw [Values.infinity_eq_zero]
    exact (map_ne_zero _).mpr (fun h => hg (eVF_injective P (h.trans (eVF_eq P 0 ▸ (map_zero _).symm))))
  have h := gamma_of_ambient P g hg ⟨_, hne⟩ rfl
  exact congrArg Subtype.val h

/-- **Valuations of concrete points in the ambient.** -/
theorem lt_value_eVF_iff (β : ℚ) (y : Ser) :
    (qpow π β).val < Values.vfValueHom (eVF P y) ↔ (β : WithTop ℚ) < ordS y := by
  by_cases hy : y = 0
  · subst hy
    have h0 : eVF P 0 = 0 := by rw [eVF_eq, map_zero]
    rw [h0, ordS_zero]
    exact iff_of_true (gamma_lt_value_zero _) (WithTop.coe_lt_top β)
  · have hy' : (y : HahnSeries ℚ ℂ) ≠ 0 := fun h => hy (Subtype.ext h)
    rw [value_eVF P y hy, ordS, ← HahnSeries.order_eq_orderTop_of_ne_zero hy', WithTop.coe_lt_coe]
    exact Hm.qpow_lt_iff P

/-! ### The Galois action and rationality -/

theorem fixed_iff_rational (m : ℕ+) (f : Ser) :
    puiseuxRootSystemAction (levelRoots m) f = f ↔ IsRational m f := by
  constructor
  · intro h γ hγ
    have h1 := congrArg (fun g : Ser => cf g γ) h
    simp only [cf_action] at h1
    have h2 : ((compatibleRootCharacter (levelRoots m) (Multiplicative.ofAdd γ) : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hγ (h1.trans (one_mul _).symm)
      exact this
    exact (char_levelRoots_eq_one_iff m γ).mp (Units.val_eq_one.mp h2)
  · intro h
    apply Subtype.ext
    ext γ
    change cf (puiseuxRootSystemAction (levelRoots m) f) γ = cf f γ
    rw [cf_action]
    by_cases hγ : cf f γ = 0
    · rw [hγ, mul_zero]
    · rw [(char_levelRoots_eq_one_iff m γ).mpr (h γ hγ), Units.val_one, one_mul]

theorem labelFixed_iff (m : ℕ+) (r : RV) : rvAction (levelRoots m) r = r ↔ LabelRational m r := by
  cases r with
  | none =>
    exact iff_of_true rfl (fun u hu => absurd hu (by simp))
  | some u =>
    rw [levelRoots_fixes_iff]
    constructor
    · rintro ⟨z, hz⟩ u' hu'
      cases Option.some.inj hu'
      exact ⟨z, hz⟩
    · intro h
      exact h u rfl

/-! ### Concrete images of ambient maps -/

section Images

variable {l' : ℕ} {A : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N)}
  {B : DefSet (rawMixedSpace (M := P.N) n l') (P.G.real : Set P.N)}

/-- The reindexing of a pair of mixed code tuples. -/
def pairIdx (n l l' : ℕ) : (Fin n ⊕ Fin l) ⊕ (Fin n ⊕ Fin l') → Fin ((n + l) + (n + l')) :=
  fun s => finSumFinEquiv (Sum.map finSumFinEquiv finSumFinEquiv s)

theorem append_comp_pairIdx {K : Type} (u : Fin (n + l) → K) (v : Fin (n + l') → K) :
    Fin.append u v ∘ pairIdx n l l' = Sum.elim (u ∘ finSumFinEquiv) (v ∘ finSumFinEquiv) := by
  funext s
  cases s with
  | inl a => simp [pairIdx, Fin.append_left]
  | inr b => simp [pairIdx, Fin.append_right]

/-- The graph of `f` as a set of raw tuples. -/
def graphRaw (f : Map A B) : Set (Fin ((n + l) + (n + l')) → P.N) :=
  {w | w ∘ pairIdx n l l' ∈ (rawMixedSpace (M := P.N) n l).relation (rawMixedSpace (M := P.N) n l')
    (fun x y => ∃ a : A, a.val = x ∧ (f a).val = y)}

theorem graphRaw_definable (f : Map A B) :
    (Set.range (P.e ∘ laurentCoefficientEnumeration)).Definable LRV (graphRaw P f) := by
  have h := f.graph_definable.preimage_comp (pairIdx n l l')
  have hB : ((P.G.real : Set P.N)) = Set.range (P.e ∘ laurentCoefficientEnumeration) := P.hB
  exact hB ▸ h

/-- A concrete point decoded from a sorted raw tuple. -/
def decodeRaw (z : Fin (n + l') → Carrier) : (Fin n → Ser) × (Fin l' → RV) :=
  (fun i => vfPart (z (Fin.castAdd l' i)), fun j => rvPart (z (Fin.natAdd n j)))

theorem mixedRaw_decodeRaw {z : Fin (n + l') → Carrier} (hz : ∀ i, sortEval (mixedSorts n l' i) (z i)) :
    mixedRaw (decodeRaw z) = z := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · rw [mixedRaw, Fin.append_left]
    have h := hz (Fin.castAdd l' a)
    have hs : mixedSorts n l' (Fin.castAdd l' a) = .vf := by simp [mixedSorts]
    rw [hs] at h
    exact vfType_tag ⟨_, h⟩
  · rw [mixedRaw, Fin.append_right]
    have h := hz (Fin.natAdd n b)
    have hs : mixedSorts n l' (Fin.natAdd n b) = .rv := by simp [mixedSorts]
    rw [hs] at h
    exact rvSort_tag ⟨_, h⟩

theorem mem_relation_mixed (R : Mixed P.N n l → Mixed P.N n l' → Prop) (x : Mixed P.N n l)
    (y : Mixed P.N n l') :
    (Sum.elim (mixedValues x) (mixedValues y) : (Fin n ⊕ Fin l) ⊕ (Fin n ⊕ Fin l') → P.N) ∈
      (rawMixedSpace (M := P.N) n l).relation (rawMixedSpace (M := P.N) n l') R ↔ R x y := by
  constructor
  · rintro ⟨hx, hy, h⟩
    have e1 : (rawMixedSpace (M := P.N) n l).decode ⟨_, hx⟩ = x := by
      have : (⟨Sum.elim (mixedValues x) (mixedValues y) ∘ Sum.inl, hx⟩ :
          (rawMixedSpace (M := P.N) n l).domain) = ⟨mixedValues x, mixedValues_mem_domain x⟩ := rfl
      rw [this, decode_mixedValues]
    have e2 : (rawMixedSpace (M := P.N) n l').decode ⟨_, hy⟩ = y := by
      have : (⟨Sum.elim (mixedValues x) (mixedValues y) ∘ Sum.inr, hy⟩ :
          (rawMixedSpace (M := P.N) n l').domain) = ⟨mixedValues y, mixedValues_mem_domain y⟩ := rfl
      rw [this, decode_mixedValues]
    rw [e1, e2] at h
    exact h
  · intro h
    refine ⟨mixedValues_mem_domain x, mixedValues_mem_domain y, ?_⟩
    have e1 : (rawMixedSpace (M := P.N) n l).decode ⟨mixedValues x, mixedValues_mem_domain x⟩ = x :=
      decode_mixedValues x
    have e2 : (rawMixedSpace (M := P.N) n l').decode ⟨mixedValues y, mixedValues_mem_domain y⟩ = y :=
      decode_mixedValues y
    change R ((rawMixedSpace (M := P.N) n l).decode ⟨mixedValues x, mixedValues_mem_domain x⟩)
      ((rawMixedSpace (M := P.N) n l').decode ⟨mixedValues y, mixedValues_mem_domain y⟩)
    rw [e1, e2]
    exact h

theorem mem_graphRaw_iff (f : Map A B) (p : (Fin n → Ser) × (Fin l → RV))
    (p' : (Fin n → Ser) × (Fin l' → RV)) :
    Fin.append (P.e ∘ mixedRaw p) (P.e ∘ mixedRaw p') ∈ graphRaw P f ↔
      ∃ h : ePoint P p ∈ A.carrier, (f ⟨ePoint P p, h⟩).val = ePoint P p' := by
  change Fin.append (P.e ∘ mixedRaw p) (P.e ∘ mixedRaw p') ∘ pairIdx n l l' ∈
    (rawMixedSpace (M := P.N) n l).relation (rawMixedSpace (M := P.N) n l')
      (fun x y => ∃ a : A, a.val = x ∧ (f a).val = y) ↔ _
  rw [append_comp_pairIdx]
  have h1 : (P.e ∘ mixedRaw p) ∘ finSumFinEquiv = mixedValues (ePoint P p) := (mixedValues_ePoint P p).symm
  have h2 : (P.e ∘ mixedRaw p') ∘ finSumFinEquiv = mixedValues (ePoint P p') := (mixedValues_ePoint P p').symm
  rw [h1, h2, mem_relation_mixed]
  constructor
  · rintro ⟨a, ha, hfa⟩
    refine ⟨ha ▸ a.property, ?_⟩
    rw [← hfa]
    have : (⟨ePoint P p, ha ▸ a.property⟩ : A) = a := Subtype.ext ha.symm
    rw [this]
  · rintro ⟨h, hf⟩
    exact ⟨⟨ePoint P p, h⟩, rfl, hf⟩

theorem e_sorted_of_mixed {z : Fin (n + l') → Carrier}
    (hz : (P.e ∘ z) ∘ finSumFinEquiv ∈ (rawMixedSpace (M := P.N) n l').domain) (i : Fin (n + l')) :
    sortEval (mixedSorts n l' i) (z i) := by
  obtain ⟨⟨x, hx⟩, ⟨u, hu⟩⟩ := hz
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · have h := congrFun hx a
    have hs : mixedSorts n l' (Fin.castAdd l' a) = .vf := by simp [mixedSorts]
    rw [hs, ← e_sort P]
    change sortEval .vf ((((P.e ∘ z) ∘ finSumFinEquiv) ∘ Sum.inl) a)
    rw [← h]
    exact (x a).property
  · have h := congrFun hu b
    have hs : mixedSorts n l' (Fin.natAdd n b) = .rv := by simp [mixedSorts]
    rw [hs, ← e_sort P]
    change sortEval .rv ((((P.e ∘ z) ∘ finSumFinEquiv) ∘ Sum.inr) b)
    rw [← h]
    exact (u b).property

/-- **The image of a concrete point is concrete.** -/
theorem exists_concrete_image (f : Map A B) (p : (Fin n → Ser) × (Fin l → RV))
    (hp : ePoint P p ∈ A.carrier) :
    ∃ p' : (Fin n → Ser) × (Fin l' → RV), (f ⟨ePoint P p, hp⟩).val = ePoint P p' := by
  have hex : ∃ y : Fin (n + l') → P.N, Fin.append (P.e ∘ mixedRaw p) y ∈ graphRaw P f := by
    refine ⟨mixedValues (f ⟨ePoint P p, hp⟩).val ∘ finSumFinEquiv.symm, ?_⟩
    change Fin.append (P.e ∘ mixedRaw p) (mixedValues (f ⟨ePoint P p, hp⟩).val ∘ finSumFinEquiv.symm) ∘
      pairIdx n l l' ∈ (rawMixedSpace (M := P.N) n l).relation (rawMixedSpace (M := P.N) n l')
        (fun x y => ∃ a : A, a.val = x ∧ (f a).val = y)
    rw [append_comp_pairIdx]
    have h1 : (P.e ∘ mixedRaw p) ∘ finSumFinEquiv = mixedValues (ePoint P p) := (mixedValues_ePoint P p).symm
    have h2 : (mixedValues (f ⟨ePoint P p, hp⟩).val ∘ finSumFinEquiv.symm) ∘ finSumFinEquiv =
        mixedValues (f ⟨ePoint P p, hp⟩).val := by
      funext s; simp
    rw [h1, h2, mem_relation_mixed]
    exact ⟨⟨ePoint P p, hp⟩, rfl, rfl⟩
  obtain ⟨y', hy'⟩ := TraceProjection.trace_exists P.e laurentCoefficientEnumeration
    (graphRaw_definable P f) (mixedRaw p) hex
  have hdom : (P.e ∘ y') ∘ finSumFinEquiv ∈ (rawMixedSpace (M := P.N) n l').domain := by
    obtain ⟨_, hy, _⟩ := hy'
    rw [append_comp_pairIdx] at hy
    exact hy
  have hsort := e_sorted_of_mixed P hdom
  refine ⟨decodeRaw y', ?_⟩
  have hy'' : Fin.append (P.e ∘ mixedRaw p) (P.e ∘ mixedRaw (decodeRaw y')) ∈ graphRaw P f := by
    rw [mixedRaw_decodeRaw hsort]
    exact hy'
  obtain ⟨_, hf⟩ := (mem_graphRaw_iff P f p _).mp hy''
  exact hf

/-- The Galois action on a concrete point. -/
def actPoint {k : ℕ} (η : CompatibleRoots ℂ) (p : (Fin n → Ser) × (Fin k → RV)) : (Fin n → Ser) × (Fin k → RV) :=
  (fun i => puiseuxRootSystemAction η (p.1 i), fun j => rvAction η (p.2 j))

theorem act_mixedRaw {k : ℕ} (η : CompatibleRoots ℂ) (p : (Fin n → Ser) × (Fin k → RV)) :
    carrierAction η ∘ mixedRaw p = mixedRaw (actPoint η p) := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [Function.comp_apply, mixedRaw, Fin.append_left, carrierAction_inl]
    rfl
  · simp only [Function.comp_apply, mixedRaw, Fin.append_right, PuiseuxOriginal.carrierAction_inr]
    rfl

/-- A concrete point is `m`-rational: rational coordinates and labels. -/
def RationalPoint {k : ℕ} (m : ℕ+) (p : (Fin n → Ser) × (Fin k → RV)) : Prop :=
  (∀ i, IsRational m (p.1 i)) ∧ ∀ j, LabelRational m (p.2 j)

theorem actPoint_eq_iff {k : ℕ} (m : ℕ+) (p : (Fin n → Ser) × (Fin k → RV)) :
    actPoint (levelRoots m) p = p ↔ RationalPoint m p := by
  constructor
  · intro h
    refine ⟨fun i => (fixed_iff_rational m _).mp (congrFun (congrArg Prod.fst h) i),
      fun j => (labelFixed_iff m _).mp (congrFun (congrArg Prod.snd h) j)⟩
  · rintro ⟨h1, h2⟩
    refine Prod.ext (funext fun i => (fixed_iff_rational m _).mpr (h1 i))
      (funext fun j => (labelFixed_iff m _).mpr (h2 j))

theorem ePoint_injective {k : ℕ} : Function.Injective (ePoint P (n := n) (l := k)) := by
  intro p q h
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · exact eVF_injective P (congrFun (congrArg Prod.fst h) i)
  · have h1 := congrArg Subtype.val (congrFun (congrArg Prod.snd h) j)
    exact Sum.inr_injective (P.e.injective h1)

theorem graphTrace_definable (f : Map A B) :
    {c | baseCarrier c}.Definable LRV {z : Fin ((n + l) + (n + l')) → Carrier | P.e ∘ z ∈ graphRaw P f} := by
  have h := (elementaryActualDefinableEquiv P.e laurentCoefficientEnumeration
    (⟨graphRaw P f, graphRaw_definable P f⟩ : LRV.DefinableSet _ (Fin ((n + l) + (n + l'))))).property
  have h' : (Set.range laurentCoefficientEnumeration).Definable LRV
      {z : Fin ((n + l) + (n + l')) → Carrier | P.e ∘ z ∈ graphRaw P f} := h
  rw [laurentCoefficientEnumeration_range] at h'
  exact h'

/-- **Images of `m`-rational concrete points are `m`-rational.** -/
theorem concrete_image_rational (f : Map A B) (m : ℕ+) (p : (Fin n → Ser) × (Fin l → RV))
    (hp : ePoint P p ∈ A.carrier) (p' : (Fin n → Ser) × (Fin l' → RV))
    (hf : (f ⟨ePoint P p, hp⟩).val = ePoint P p') (hrat : RationalPoint m p) : RationalPoint m p' := by
  have hmem : Fin.append (mixedRaw p) (mixedRaw p') ∈
      {z : Fin ((n + l) + (n + l')) → Carrier | P.e ∘ z ∈ graphRaw P f} := by
    change P.e ∘ Fin.append (mixedRaw p) (mixedRaw p') ∈ graphRaw P f
    have he : P.e ∘ Fin.append (mixedRaw p) (mixedRaw p') = Fin.append (P.e ∘ mixedRaw p) (P.e ∘ mixedRaw p') := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [Fin.append_left, Fin.append_right]
    rw [he]
    exact (mem_graphRaw_iff P f p p').mpr ⟨hp, hf⟩
  have hact := (raw_original_definable_invariant (levelRoots m) _ (graphTrace_definable P f) _).mpr hmem
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
  change P.e ∘ Fin.append (mixedRaw p) (mixedRaw (actPoint (levelRoots m) p')) ∈ graphRaw P f at hact
  have he : P.e ∘ Fin.append (mixedRaw p) (mixedRaw (actPoint (levelRoots m) p')) =
      Fin.append (P.e ∘ mixedRaw p) (P.e ∘ mixedRaw (actPoint (levelRoots m) p')) := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [Fin.append_left, Fin.append_right]
  rw [he] at hact
  obtain ⟨_, hf'⟩ := (mem_graphRaw_iff P f p _).mp hact
  have hfix : actPoint (levelRoots m) p' = p' := ePoint_injective P (hf'.symm.trans hf)
  exact (actPoint_eq_iff m p').mp hfix

end Images

end DiamondIntegral.Section8.Truncation
