import «section 8».TruncFull

/-! Invariance of truncation classes under maps respecting truncations.

`fullClass_eq_of_correspondence`: let `Φ` map the rational integral points of `X` bijectively onto
those of `Y`, such that two points have the same truncation iff their images do, and such that the
induced relation on truncations is definable. Then `Θ([X[m;β]]) [𝔸]^{-mΣβ} = Θ([Y[m;β]]) [𝔸]^{-mΣβ}`:
the induced map is a definable bijection of the truncation sets (`resSetClass_bijection`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section4 DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal

local instance invStructure : LRV.Structure Carrier := canonicalInterpret
local instance invModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable {n l l' : ℕ} (m : ℕ+) (b : Fin n → ℕ)

/-- A rational integral concrete point. -/
def RI {k : ℕ} (p : (Fin n → Ser) × (Fin k → RV)) : Prop :=
  (∀ i, IsRational m (p.1 i) ∧ IsIntegral (p.1 i)) ∧ ∀ j, LabelRational m (p.2 j)

/-- The truncation of a point, as an RV tuple. -/
def truncOf {k : ℕ} (p : (Fin n → Ser) × (Fin k → RV)) : Fin (Kt b k) → CanonicalRV.RVSort Carrier :=
  fun i => rvTag ((Sum.elim (truncPoint m b p.1) p.2) ((εt b k).symm i))

theorem mem_fullTruncSet_iff {k : ℕ} (A : Set ((Fin n → Ser) × (Fin k → RV)))
    (r : Fin (Kt b k) → CanonicalRV.RVSort Carrier) :
    r ∈ fullTruncSet m b A ↔ ∃ p ∈ A, RI m p ∧ r = truncOf m b p := by
  constructor
  · rintro ⟨p, hp, hr, hu, hw⟩
    refine ⟨p, hp, ⟨hr, hu⟩, ?_⟩
    funext i
    have := congrFun hw ((εt b k).symm i)
    simp only [Equiv.apply_symm_apply] at this
    change r i = rvTag _
    rw [← this]
    exact (taggedRVEquiv.symm_apply_apply (r i)).symm
  · rintro ⟨p, hp, ⟨hr, hu⟩, rfl⟩
    refine ⟨p, hp, hr, hu, ?_⟩
    funext a
    simp only [truncOf, Equiv.symm_apply_apply]
    rfl

variable {X : Set (Fin (n + l) → Carrier)} {Y : Set (Fin (n + l') → Carrier)}

/-- **Invariance of truncation classes.** -/
theorem fullClass_eq_of_correspondence
    (Q : Finset (Fin l → ℤ)) (Q' : Finset (Fin l' → ℤ))
    (hX : DefinableOver {c | baseCarrier c} (mixedSorts n l) X)
    (hY : DefinableOver {c | baseCarrier c} (mixedSorts n l') Y)
    (hA : Invariant m b (mixedSet X)) (hB : Invariant m b (mixedSet Y))
    (hQ : Covers m Q (mixedSet X)) (hQ' : Covers m Q' (mixedSet Y))
    (Φ : (Fin n → Ser) × (Fin l → RV) → (Fin n → Ser) × (Fin l' → RV))
    (hmaps : ∀ p ∈ mixedSet X, RI m p → Φ p ∈ mixedSet Y ∧ RI m (Φ p))
    (hsurj : ∀ p' ∈ mixedSet Y, RI m p' → ∃ p ∈ mixedSet X, RI m p ∧ Φ p = p')
    (hresp : ∀ p ∈ mixedSet X, ∀ p' ∈ mixedSet X, RI m p → RI m p' →
      (truncOf m b p = truncOf m b p' ↔ truncOf m b (Φ p) = truncOf m b (Φ p')))
    (hgraph : (rawRVSpace (M := Carrier) (Kt b l)).RelationDefinable (rawRVSpace (M := Carrier) (Kt b l'))
      {c | baseCarrier c} (fun r r' => ∃ p ∈ mixedSet X, RI m p ∧ r = truncOf m b p ∧ r' = truncOf m b (Φ p))) :
    fullClass m b Q hX hA hQ = fullClass m b Q' hY hB hQ' := by
  let SX := fullTruncDefSet m b Q hX hA hQ
  let SY := fullTruncDefSet m b Q' hY hB hQ'
  have hpt : ∀ r : SX, ∃ p ∈ mixedSet X, RI m p ∧ r.val = truncOf m b p :=
    fun r => (mem_fullTruncSet_iff m b _ r.val).mp r.property
  choose pt hptX hptRI hptEq using hpt
  let F : SX → SY := fun r => ⟨truncOf m b (Φ (pt r)),
    (mem_fullTruncSet_iff m b _ _).mpr ⟨Φ (pt r), (hmaps _ (hptX r) (hptRI r)).1,
      (hmaps _ (hptX r) (hptRI r)).2, rfl⟩⟩
  have hF : ∀ (r : SX) (p : (Fin n → Ser) × (Fin l → RV)), p ∈ mixedSet X → RI m p →
      r.val = truncOf m b p → (F r).val = truncOf m b (Φ p) := by
    intro r p hp hRI hr
    exact (hresp _ (hptX r) _ hp (hptRI r) hRI).mp ((hptEq r).symm.trans hr)
  let f : Map SX SY := ⟨F, by
    refine (hgraph.congr _ _ ?_)
    intro r r'
    constructor
    · rintro ⟨p, hp, hRI, rfl, rfl⟩
      have hr : truncOf m b p ∈ SX.carrier := (mem_fullTruncSet_iff m b _ _).mpr ⟨p, hp, hRI, rfl⟩
      exact ⟨⟨_, hr⟩, rfl, hF ⟨_, hr⟩ p hp hRI rfl⟩
    · rintro ⟨a, rfl, rfl⟩
      exact ⟨pt a, hptX a, hptRI a, hptEq a, rfl⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro r s hrs
      apply Subtype.ext
      have h1 : (F r).val = (F s).val := congrArg Subtype.val hrs
      rw [hptEq r, hptEq s]
      exact (hresp _ (hptX r) _ (hptX s) (hptRI r) (hptRI s)).mpr h1
    · intro s
      obtain ⟨p', hp', hRI', hs⟩ := (mem_fullTruncSet_iff m b _ s.val).mp s.property
      obtain ⟨p, hp, hRI, rfl⟩ := hsurj p' hp' hRI'
      have hr : truncOf m b p ∈ SX.carrier := (mem_fullTruncSet_iff m b _ _).mpr ⟨p, hp, hRI, rfl⟩
      exact ⟨⟨_, hr⟩, Subtype.ext ((hF ⟨_, hr⟩ p hp hRI rfl).trans hs.symm)⟩
  have hcls := resSetClass_bijection canonicalInterpret_isCanonical SX SY
    (fullTruncSet_finite_values m b Q hX hA hQ) (fullTruncSet_finite_values m b Q' hY hB hQ') ⟨f, hbij⟩
  unfold fullClass
  rw [hcls]

end DiamondIntegral.Section8.Truncation
