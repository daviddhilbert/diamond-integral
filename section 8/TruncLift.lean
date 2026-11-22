import «section 8».TruncSteps
import «section 8».ThetaBridge

/-! Concrete images under ambient maps of RV sets.

For a map `f : A → B` of RV sets definable over the base of Section 8, the image of a concrete
point is the image of a concrete point (`exists_concrete_rv_image`), `m`-rational if the source
point is (`concrete_rv_image_rational`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry SpecialTransformations.Section9
open DiamondIntegral.Section2 DiamondIntegral.Section3
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.GammaCells DiamondIntegral.Section8.Galois

local instance liftStructure : LRV.Structure Carrier := canonicalInterpret
local instance liftModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable (P : PuiseuxAmbient) {a b : ℕ}

/-- The image of a concrete RV tuple. -/
def eRVs (t : Fin a → RV) : Fin a → CanonicalRV.RVSort P.N := fun j => eRV P (t j)

theorem eRVs_injective : Function.Injective (eRVs P (a := a)) := by
  intro t t' h
  funext j
  have h1 := congrArg Subtype.val (congrFun h j)
  exact Sum.inr_injective (P.e.injective h1)

/-- The raw codes of a concrete RV tuple. -/
def rvCodes (t : Fin a → RV) : Fin a → Carrier := fun j => Sum.inr (t j)

theorem e_rvCodes (t : Fin a → RV) : P.e ∘ rvCodes t = rvValues (eRVs P t) := rfl

theorem rawRV_relation_iff' {K K' : ℕ}
    (r : (Fin K → CanonicalRV.RVSort P.N) → (Fin K' → CanonicalRV.RVSort P.N) → Prop)
    (z : Fin K ⊕ Fin K' → P.N) :
    z ∈ (rawRVSpace (M := P.N) K).relation (rawRVSpace (M := P.N) K') r ↔
      ∃ x y, r x y ∧ rvValues x = z ∘ Sum.inl ∧ rvValues y = z ∘ Sum.inr := by
  constructor
  · rintro ⟨hx, hy, h⟩
    exact ⟨_, _, h, Classical.choose_spec hx, Classical.choose_spec hy⟩
  · rintro ⟨x, y, h, hx, hy⟩
    have hx' : z ∘ Sum.inl ∈ (rawRVSpace (M := P.N) K).domain := ⟨x, hx⟩
    have hy' : z ∘ Sum.inr ∈ (rawRVSpace (M := P.N) K').domain := ⟨y, hy⟩
    refine ⟨hx', hy', ?_⟩
    have dx : (rawRVSpace (M := P.N) K).decode ⟨z ∘ Sum.inl, hx'⟩ = x :=
      rvValues_injective ((Classical.choose_spec hx').trans hx.symm)
    have dy : (rawRVSpace (M := P.N) K').decode ⟨z ∘ Sum.inr, hy'⟩ = y :=
      rvValues_injective ((Classical.choose_spec hy').trans hy.symm)
    rw [dx, dy]
    exact h

variable {A : DefSet (rawRVSpace (M := P.N) a) (P.G.real : Set P.N)}
  {B : DefSet (rawRVSpace (M := P.N) b) (P.G.real : Set P.N)}

/-- The graph of a map of RV sets as raw tuples. -/
def graphRV (f : Map A B) : Set (Fin (a + b) → P.N) :=
  {w | w ∘ finSumFinEquiv ∈ (rawRVSpace (M := P.N) a).relation (rawRVSpace (M := P.N) b)
    (fun x y => ∃ c : A, c.val = x ∧ (f c).val = y)}

theorem graphRV_definable (f : Map A B) :
    (Set.range (P.e ∘ laurentCoefficientEnumeration)).Definable LRV (graphRV P f) := by
  have h := f.graph_definable.preimage_comp (finSumFinEquiv : Fin a ⊕ Fin b → Fin (a + b))
  have hB : ((P.G.real : Set P.N)) = Set.range (P.e ∘ laurentCoefficientEnumeration) := P.hB
  exact hB ▸ h

theorem mem_graphRV_iff (f : Map A B) (x : Fin a → CanonicalRV.RVSort P.N)
    (y : Fin b → CanonicalRV.RVSort P.N) :
    Fin.append (rvValues x) (rvValues y) ∈ graphRV P f ↔ ∃ h : x ∈ A.carrier, (f ⟨x, h⟩).val = y := by
  change Fin.append (rvValues x) (rvValues y) ∘ finSumFinEquiv ∈
    (rawRVSpace (M := P.N) a).relation (rawRVSpace (M := P.N) b)
      (fun x y => ∃ c : A, c.val = x ∧ (f c).val = y) ↔ _
  rw [rawRV_relation_iff']
  have h1 : (Fin.append (rvValues x) (rvValues y) ∘ finSumFinEquiv) ∘ Sum.inl = rvValues x :=
    funext fun i => by simp [Fin.append_left]
  have h2 : (Fin.append (rvValues x) (rvValues y) ∘ finSumFinEquiv) ∘ Sum.inr = rvValues y :=
    funext fun i => by simp [Fin.append_right]
  rw [h1, h2]
  constructor
  · rintro ⟨x', y', ⟨c, hc, hfc⟩, hx, hy⟩
    have ex : x' = x := rvValues_injective hx
    have ey : y' = y := rvValues_injective hy
    subst ex ey
    refine ⟨hc ▸ c.property, ?_⟩
    rw [← hfc]
    have : (⟨x', hc ▸ c.property⟩ : A) = c := Subtype.ext hc.symm
    rw [this]
  · rintro ⟨h, hf⟩
    exact ⟨x, y, ⟨⟨x, h⟩, rfl, hf⟩, rfl, rfl⟩

theorem rv_sorted_of_e {z : Fin b → Carrier} (hz : P.e ∘ z ∈ (rawRVSpace (M := P.N) b).domain) (i : Fin b) :
    z i = Sum.inr (rvPart (z i)) := by
  obtain ⟨y, hy⟩ := hz
  have h := congrFun hy i
  have hrv : iRV (P.e (z i)) := by
    change iRV ((P.e ∘ z) i)
    rw [← h]
    exact (y i).property
  exact Hm.concrete_rv P hrv

/-- **The image of a concrete RV point is concrete.** -/
theorem exists_concrete_rv_image (f : Map A B) (t : Fin a → RV) (ht : eRVs P t ∈ A.carrier) :
    ∃ s : Fin b → RV, (f ⟨eRVs P t, ht⟩).val = eRVs P s := by
  have hex : ∃ y : Fin b → P.N, Fin.append (P.e ∘ rvCodes t) y ∈ graphRV P f :=
    ⟨rvValues (f ⟨eRVs P t, ht⟩).val, (mem_graphRV_iff P f _ _).mpr ⟨ht, rfl⟩⟩
  obtain ⟨y', hy'⟩ := TraceProjection.trace_exists P.e laurentCoefficientEnumeration
    (graphRV_definable P f) (rvCodes t) hex
  have hdom : P.e ∘ y' ∈ (rawRVSpace (M := P.N) b).domain := by
    obtain ⟨_, hy, _⟩ := hy'
    have h2 : (Fin.append (P.e ∘ rvCodes t) (P.e ∘ y') ∘ finSumFinEquiv) ∘ Sum.inr = P.e ∘ y' :=
      funext fun i => by simp [Fin.append_right]
    rw [← h2]
    exact hy
  have hy'' : y' = rvCodes (fun i => rvPart (y' i)) := funext fun i => rv_sorted_of_e P hdom i
  refine ⟨fun i => rvPart (y' i), ?_⟩
  rw [hy''] at hy'
  obtain ⟨_, hf⟩ := (mem_graphRV_iff P f (eRVs P t) (eRVs P (fun i => rvPart (y' i)))).mp hy'
  exact hf

theorem graphRV_trace_definable (f : Map A B) :
    {c | baseCarrier c}.Definable LRV {z : Fin (a + b) → Carrier | P.e ∘ z ∈ graphRV P f} := by
  have h := (elementaryActualDefinableEquiv P.e laurentCoefficientEnumeration
    (⟨graphRV P f, graphRV_definable P f⟩ : LRV.DefinableSet _ (Fin (a + b)))).property
  have h' : (Set.range laurentCoefficientEnumeration).Definable LRV
      {z : Fin (a + b) → Carrier | P.e ∘ z ∈ graphRV P f} := h
  rw [laurentCoefficientEnumeration_range] at h'
  exact h'

theorem e_append_rvCodes (t : Fin a → RV) (s : Fin b → RV) :
    P.e ∘ Fin.append (rvCodes t) (rvCodes s) = Fin.append (rvValues (eRVs P t)) (rvValues (eRVs P s)) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [Fin.append_left, Fin.append_right, rvCodes]
  · rfl
  · rfl

/-- **Images of `m`-rational concrete RV points are `m`-rational.** -/
theorem concrete_rv_image_rational (f : Map A B) (m : ℕ+) (t : Fin a → RV) (ht : eRVs P t ∈ A.carrier)
    (s : Fin b → RV) (hs : (f ⟨eRVs P t, ht⟩).val = eRVs P s) (hrat : ∀ j, LabelRational m (t j)) :
    ∀ i, LabelRational m (s i) := by
  have hmem : Fin.append (rvCodes t) (rvCodes s) ∈
      {z : Fin (a + b) → Carrier | P.e ∘ z ∈ graphRV P f} := by
    change P.e ∘ Fin.append (rvCodes t) (rvCodes s) ∈ graphRV P f
    rw [e_append_rvCodes]
    exact (mem_graphRV_iff P f _ _).mpr ⟨ht, hs⟩
  have hact := (raw_original_definable_invariant (levelRoots m) _ (graphRV_trace_definable P f) _).mpr hmem
  have hcomp : carrierAction (levelRoots m) ∘ Fin.append (rvCodes t) (rvCodes s) =
      Fin.append (rvCodes t) (rvCodes (fun i => rvAction (levelRoots m) (s i))) := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [Function.comp_apply, Fin.append_left, rvCodes]
      rw [PuiseuxOriginal.carrierAction_inr, (labelFixed_iff m (t i)).mpr (hrat i)]
    · simp only [Function.comp_apply, Fin.append_right, rvCodes]
      rw [PuiseuxOriginal.carrierAction_inr]
  rw [hcomp] at hact
  change P.e ∘ Fin.append (rvCodes t) (rvCodes (fun i => rvAction (levelRoots m) (s i))) ∈ graphRV P f at hact
  rw [e_append_rvCodes] at hact
  obtain ⟨_, hf⟩ := (mem_graphRV_iff P f _ _).mp hact
  have hfix := eRVs_injective P (hf.symm.trans hs)
  intro i
  exact (labelFixed_iff m (s i)).mp (congrFun hfix i)

/-! ### Reindexing bijections of concrete RV sets -/

/-- **A coordinate selection that is bijective between two RV sets preserves the class.** -/
theorem resSetClass_reindex {K1 K2 : ℕ} (A : DefSet (rawRVSpace (M := Carrier) K1) {c | baseCarrier c})
    (B : DefSet (rawRVSpace (M := Carrier) K2) {c | baseCarrier c})
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hB : (Set.range (fun u : B => fun i => Values.vrv (u.val i))).Finite)
    (π : Fin K2 → Fin K1) (hmaps : ∀ r ∈ A.carrier, (fun j => r (π j)) ∈ B.carrier)
    (hinj : ∀ r ∈ A.carrier, ∀ r' ∈ A.carrier, (fun j => r (π j)) = (fun j => r' (π j)) → r = r')
    (hsurj : ∀ s ∈ B.carrier, ∃ r ∈ A.carrier, (fun j => r (π j)) = s) :
    resSetClass canonicalInterpret_isCanonical A hA = resSetClass canonicalInterpret_isCanonical B hB := by
  let F : A → B := fun r => ⟨fun j => r.val (π j), hmaps r.val r.property⟩
  have hgraph : (rawRVSpace (M := Carrier) K1).RelationDefinable (rawRVSpace (M := Carrier) K2)
      {c | baseCarrier c} (fun x y => ∃ a : A, a.val = x ∧ (F a).val = y) := by
    have hAd : {c | baseCarrier c}.Definable LRV ((rawRVSpace (M := Carrier) K1).preimage A.carrier) :=
      A.definable
    have hdom : {c | baseCarrier c}.Definable LRV (rawRVSpace (M := Carrier) K2).domain :=
      (rawRVSpace (M := Carrier) K2).definable_domain _
    have heq : {c | baseCarrier c}.Definable LRV
        {z : Fin K1 ⊕ Fin K2 → Carrier | ∀ j, z (.inr j) = z (.inl (π j))} := by
      convert Set.definable_iInter_of_finite fun j : Fin K2 =>
        (Set.DefinableFun.proj (L := LRV) (A := {c : Carrier | baseCarrier c})
          (i := (Sum.inr j : Fin K1 ⊕ Fin K2))).ofPred_eq
        (Set.DefinableFun.proj (L := LRV) (A := {c : Carrier | baseCarrier c})
          (i := (Sum.inl (π j) : Fin K1 ⊕ Fin K2))) using 1
      ext z
      simp
    change {c | baseCarrier c}.Definable LRV ((rawRVSpace (M := Carrier) K1).relation
      (rawRVSpace (M := Carrier) K2) (fun x y => ∃ a : A, a.val = x ∧ (F a).val = y))
    convert (hAd.preimage_comp Sum.inl).inter ((hdom.preimage_comp Sum.inr).inter heq) using 1
    ext z
    rw [rawRV_relation_iff]
    constructor
    · rintro ⟨x, y, ⟨a, rfl, rfl⟩, hx, hy⟩
      refine ⟨?_, ?_, fun j => ?_⟩
      · rw [Set.mem_preimage, ← hx]
        exact (rawRV_preimage_iff _ _).mpr ⟨a.val, a.property, rfl⟩
      · rw [Set.mem_preimage, ← hy]
        exact ⟨_, rfl⟩
      · have h1 := congrFun hy j
        have h2 := congrFun hx (π j)
        change z (Sum.inr j) = z (Sum.inl (π j))
        change (a.val (π j)).val = z (Sum.inr j) at h1
        change (a.val (π j)).val = z (Sum.inl (π j)) at h2
        rw [← h1, ← h2]
    · rintro ⟨hl, hr, heqz⟩
      obtain ⟨x, hx, hxz⟩ := (rawRV_preimage_iff _ _).mp hl
      obtain ⟨y, hyz⟩ := hr
      refine ⟨x, y, ⟨⟨x, hx⟩, rfl, ?_⟩, hxz, hyz⟩
      funext j
      apply Subtype.ext
      have h1 := congrFun hyz j
      have h2 := congrFun hxz (π j)
      have h3 := heqz j
      change (y j).val = z (Sum.inr j) at h1
      change (x (π j)).val = z (Sum.inl (π j)) at h2
      change (x (π j)).val = (y j).val
      rw [h2, h1, h3]
  have hbij : Function.Bijective (⟨F, hgraph⟩ : Map A B) := by
    constructor
    · intro r r' h
      exact Subtype.ext (hinj r.val r.property r'.val r'.property (congrArg Subtype.val h))
    · intro s
      obtain ⟨r, hr, hrs⟩ := hsurj s.val s.property
      exact ⟨⟨r, hr⟩, Subtype.ext hrs⟩
  exact resSetClass_bijection canonicalInterpret_isCanonical A B hA hB ⟨⟨F, hgraph⟩, hbij⟩

/-! ### The concrete value map of a measured RV object -/

variable {n : ℕ} (U : DiamondIntegral.Section6.MeasuredRVObject (M := P.N) (P.G.real : Set P.N) n)

/-- The concrete value of a concrete point of `U`. -/
def fcv (t : Fin U.object.arity → RV) (ht : eRVs P t ∈ U.object.domain.carrier) : Fin n → RV :=
  Classical.choose (exists_concrete_rv_image P U.object.volume t ht)

theorem fcv_spec (t : Fin U.object.arity → RV) (ht : eRVs P t ∈ U.object.domain.carrier) :
    U.object.value ⟨eRVs P t, ht⟩ = eRVs P (fcv P U t ht) :=
  Classical.choose_spec (exists_concrete_rv_image P U.object.volume t ht)

theorem encodedRv_eVF (y : Ser) : CanonicalRV.encodedRv (eVF P y) = eRV P (rvOfField y) := by
  apply Subtype.ext
  change iRv (P.e (Sum.inl y)) = P.e (Sum.inr (rvOfField y))
  rw [← e_iRv, iRv_inl]

/-- **The concrete points of the scaled lift.** -/
theorem mem_lift (L : ℕ) (x : Fin n → Ser) (t : Fin U.object.arity → RV) :
    (x, t) ∈ mixedSet (strace P L (SpecialTransformations.Section4.rvLift U.object)) ↔
      ∃ ht : eRVs P t ∈ U.object.domain.carrier, ∀ i, rvOfField (tInv L * x i) = fcv P U t ht i := by
  rw [mem_strace]
  change (∃ u : U.object.domain, u.val = eRVs P t ∧
    U.object.value u = SpecialTransformations.Section4.tupleRV (fun i => eVF P (tInv L * x i))) ↔ _
  have htup : SpecialTransformations.Section4.tupleRV (fun i => eVF P (tInv L * x i)) = eRVs P (fun i => rvOfField (tInv L * x i)) :=
    funext fun i => encodedRv_eVF P _
  rw [htup]
  constructor
  · rintro ⟨u, hu, hv⟩
    have ht : eRVs P t ∈ U.object.domain.carrier := hu ▸ u.property
    refine ⟨ht, fun i => ?_⟩
    have he : u = ⟨eRVs P t, ht⟩ := Subtype.ext hu
    rw [he, fcv_spec] at hv
    exact (congrFun (eRVs_injective P hv) i).symm
  · rintro ⟨ht, hx⟩
    refine ⟨⟨eRVs P t, ht⟩, rfl, ?_⟩
    rw [fcv_spec]
    congr 1
    funext i
    exact (hx i).symm

end DiamondIntegral.Section8.Truncation
