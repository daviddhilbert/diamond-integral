import «section 8».TruncStep
import «section 6».UniformMixedRadius

/-! Concrete bounds for proper invariant ambient sets.

For a set `B` definable over the base of Section 8 in the ambient model:

* `vf_lower_bound`: if `B` is VF-bounded, the concrete points of `B` have valuations `≥ -N` for a
  natural number `N` (elementarity applied to a witness of the bound);
* `rationalIntegral_strace`: hence the rational points of `t^L B(ℂ((t)))` are integral for `L ≥ N`;
* `label_bounds`, `labelsNonzero_strace`, `covers_strace`: if the RV support of `B` is doubly bounded,
  the labels of its concrete points have values in a bounded rational interval, are nonzero, and
  finitely many label patterns cover the rational points;
* `radius_rational`: a uniform named invariance radius of a proper invariant set is a rational power
  of `π`, so `B` is invariant at the radii `π^{b_i/m − L}` once `b_i/m − L` is large. -/

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
open DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.GammaCells

local instance goodStructure : LRV.Structure Carrier := canonicalInterpret
local instance goodModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

/-! ### Definability of universally bounded sets -/

section General

variable {M : Type} [LRV.Structure M] {S : Set M}

theorem forall_le_definable {k : ℕ} {K : Type} [Finite K] {C : Set (K → M)} (hC : S.Definable LRV C)
    (a b : (Fin k ⊕ K → M) → M) (ha : S.DefinableFun LRV a) (hb : S.DefinableFun LRV b) :
    S.Definable LRV {y : Fin k → M | ∀ w ∈ C, iLe (a (Sum.elim y w)) (b (Sum.elim y w))} := by
  let H : Set (Fin k ⊕ K → M) := {v | v ∘ Sum.inr ∈ C ∧ ¬ iLe (a v) (b v)}
  have hle : S.Definable LRV {v : Fin k ⊕ K → M | iLe (a v) (b v)} :=
    (raw_le_definable S).preimage_map (F := fun v => ![a v, b v]) (fun i => by fin_cases i; exacts [ha, hb])
  have hH : S.Definable LRV H := (hC.preimage_comp Sum.inr).inter hle.compl
  have himg := (hH.image_comp Sum.inl).compl
  convert himg using 1
  ext y
  constructor
  · rintro h ⟨v, ⟨hv1, hv2⟩, hvy⟩
    apply hv2
    have he : Sum.elim y (v ∘ Sum.inr) = v := by
      rw [← hvy]
      exact Sum.elim_comp_inl_inr v
    have := h (v ∘ Sum.inr) hv1
    rwa [he] at this
  · intro h w hw
    by_contra hn
    exact h ⟨Sum.elim y w, ⟨hw, hn⟩, Sum.elim_comp_inl y w⟩

theorem nonzeroRV_definable : S.Definable LRV {y : Fin 1 → M | iRV (y 0) ∧ y 0 ≠ iRVZero} := by
  have hs : S.Definable LRV {y : Fin 1 → M | sortEval .rv (y 0)} :=
    ((definableAt_sort S .rv).raw_definable)
  have hz : S.Definable LRV {y : Fin 1 → M | y 0 = iRVZero} :=
    (Set.DefinableFun.proj (L := LRV) (A := S) (i := (0 : Fin 1))).ofPred_eq
      ((Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvZero)).comp
        (fun a => a.elim0))
  convert hs.inter hz.compl using 1
  ext y
  exact Iff.rfl

end General

/-! ### Transfer through the elementary embedding -/

variable (P : PuiseuxAmbient)

local notation "π" => uniformizerValue P

theorem e_iRv (x : Carrier) : P.e (iRv x) = iRv (P.e x) := by
  have h := P.e.map_fun Fn.rvMap ![x]
  have ht : (P.e ∘ (![x] : Fin 1 → Carrier)) = ![P.e x] := by funext i; fin_cases i; rfl
  rw [ht] at h
  exact h

theorem e_iLe (x y : Carrier) : iLe (P.e x) (P.e y) ↔ iLe x y := by
  have h := P.e.map_rel Rel.rvLe ![x, y]
  have ht : (P.e ∘ (![x, y] : Fin 2 → Carrier)) = ![P.e x, P.e y] := by funext i; fin_cases i <;> rfl
  rw [ht] at h
  exact h

theorem e_iRVZero : P.e (iRVZero : Carrier) = iRVZero := by
  have h := P.e.map_fun Fn.rvZero (fun i : Fin 0 => i.elim0)
  have ht : (P.e ∘ (fun i : Fin 0 => i.elim0 : Fin 0 → Carrier)) = fun i => i.elim0 := funext fun i => i.elim0
  rw [ht] at h
  exact h

/-- **A nonempty definable set has a concrete point.** -/
theorem concrete_witness {k : ℕ} {G : Set (Fin k → P.N)} (hG : (P.G.real : Set P.N).Definable LRV G)
    (hne : G.Nonempty) : ∃ c : Fin k → Carrier, P.e ∘ c ∈ G := by
  let G' : Set (Fin (0 + k) → P.N) := (fun w : Fin (0 + k) → P.N => w ∘ Fin.cast (zero_add k).symm) ⁻¹' G
  have hB : ((P.G.real : Set P.N)) = Set.range (P.e ∘ laurentCoefficientEnumeration) := P.hB
  have hG' : (Set.range (P.e ∘ laurentCoefficientEnumeration)).Definable LRV G' :=
    hB ▸ hG.preimage_comp (Fin.cast (zero_add k).symm)
  obtain ⟨g, hg⟩ := hne
  have hex : ∃ y : Fin k → P.N, Fin.append (P.e ∘ (Fin.elim0 : Fin 0 → Carrier)) y ∈ G' := by
    refine ⟨g, ?_⟩
    change Fin.append (P.e ∘ (Fin.elim0 : Fin 0 → Carrier)) g ∘ Fin.cast (zero_add k).symm ∈ G
    convert hg using 1
    funext i
    simp only [Function.comp_apply]
    rw [show (Fin.cast (zero_add k).symm i : Fin (0 + k)) = Fin.natAdd 0 i from Fin.ext (by simp),
      Fin.append_right]
  obtain ⟨y, hy⟩ := TraceProjection.trace_exists P.e laurentCoefficientEnumeration hG'
    (Fin.elim0 : Fin 0 → Carrier) hex
  refine ⟨y, ?_⟩
  change Fin.append (P.e ∘ (Fin.elim0 : Fin 0 → Carrier)) (P.e ∘ y) ∘ Fin.cast (zero_add k).symm ∈ G at hy
  convert hy using 1
  funext i
  simp only [Function.comp_apply]
  rw [show (Fin.cast (zero_add k).symm i : Fin (0 + k)) = Fin.natAdd 0 i from Fin.ext (by simp),
    Fin.append_right]
  rfl

/-! ### Valuation bounds -/

variable {n l : ℕ}

theorem codes_mem (B : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N))
    (p : (Fin n → Ser) × (Fin l → RV)) (hp : p ∈ mixedSet (traceRaw P B)) :
    mixedValues (ePoint P p) ∈ (rawMixedSpace (M := P.N) n l).preimage B.carrier := by
  rw [mem_mixedSet_trace] at hp
  exact ⟨mixedValues_mem_domain _, by rwa [decode_mixedValues]⟩

theorem decode_codes (B : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N))
    {w : Fin n ⊕ Fin l → P.N} (hw : w ∈ (rawMixedSpace (M := P.N) n l).preimage B.carrier) :
    ∃ p ∈ B.carrier, mixedValues p = w := by
  obtain ⟨hz, hB⟩ := hw
  exact ⟨_, hB, mixedValues_decode ⟨w, hz⟩⟩

theorem codeValue_val {a : P.N} (ha : NonzeroRV a) : (codeValue a).val = Values.vrv ⟨a, ha.1⟩ := by
  simp only [codeValue, ha, ↓reduceDIte]
  rfl

/-- **Concrete points of a VF-bounded set have valuations bounded below.** -/
theorem vf_lower_bound (B : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N))
    (hB : DiamondIntegral.Section6.VFBounded B.carrier) :
    ∃ N : ℕ, ∀ p ∈ mixedSet (traceRaw P B), ∀ i, ((-(N : ℚ) : ℚ) : WithTop ℚ) ≤ ordS (p.1 i) := by
  let Bc := (rawMixedSpace (M := P.N) n l).preimage B.carrier
  let G : Set (Fin 1 → P.N) := {y | iRV (y 0) ∧ y 0 ≠ iRVZero} ∩
    ⋂ i : Fin n, {y | ∀ w ∈ Bc, iLe ((fun v : Fin 1 ⊕ (Fin n ⊕ Fin l) → P.N => v (.inl 0)) (Sum.elim y w))
      ((fun v : Fin 1 ⊕ (Fin n ⊕ Fin l) → P.N => iRv (v (.inr (.inl i)))) (Sum.elim y w))}
  have hG : (P.G.real : Set P.N).Definable LRV G := by
    refine nonzeroRV_definable.inter (Set.definable_iInter_of_finite fun i => ?_)
    refine forall_le_definable B.definable (fun v => v (.inl 0)) (fun v => iRv (v (.inr (.inl i))))
      (Set.DefinableFun.proj LRV) ?_
    exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := P.N) (L := LRV) Fn.rvMap)).comp
      (fun a => by fin_cases a; exact Set.DefinableFun.proj LRV)
  obtain ⟨γ, hγ⟩ := hB
  obtain ⟨a, ha, haγ⟩ := SpecialTransformations.Section3.GammaParameters.EndpointLogic.codeValue_surjective γ
  have hne : G.Nonempty := by
    refine ⟨fun _ => a, ⟨ha.1, ha.2⟩, Set.mem_iInter.mpr fun i => ?_⟩
    intro w hw
    obtain ⟨p, hp, rfl⟩ := decode_codes P B hw
    have h1 := hγ p hp i
    rw [← haγ, codeValue_val P ha] at h1
    exact (Values.vrv_le_iff _ _).mp h1
  obtain ⟨c, hc⟩ := concrete_witness P hG hne
  obtain ⟨⟨hrv, hnz⟩, hall⟩ := hc
  have hrv' : sortEval .rv (c 0) := (e_sort P .rv (c 0)).mp hrv
  obtain ⟨r, hr⟩ : ∃ r : RV, c 0 = Sum.inr r := by
    rcases hc0 : c 0 with f | r
    · rw [hc0] at hrv'
      exact absurd hrv' (fun h => h trivial)
    · exact ⟨r, rfl⟩
  have hrz : r ≠ none := by
    intro h
    apply hnz
    change P.e (c 0) = iRVZero
    rw [hr, h, ← e_iRVZero]
    rfl
  obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.mp hrz
  refine ⟨⌈-(Multiplicative.toAdd u.1)⌉₊, fun p hp i => ?_⟩
  have h1 := (Set.mem_iInter.mp hall i) _ (codes_mem P B p hp)
  change iLe (P.e (c 0)) (iRv (P.e (Sum.inl (p.1 i)))) at h1
  rw [← e_iRv, e_iLe, hr, iRv_inl] at h1
  have h2 := (iLe_rvTag (some u) (rvOfField (p.1 i))).mp h1
  rw [rvOfField_value] at h2
  refine le_trans ?_ h2
  change ((-(⌈-(Multiplicative.toAdd u.1)⌉₊ : ℚ) : ℚ) : WithTop ℚ) ≤ ((Multiplicative.toAdd u.1 : ℚ) : WithTop ℚ)
  rw [WithTop.coe_le_coe]
  have := Nat.le_ceil (-(Multiplicative.toAdd u.1))
  linarith

theorem isIntegral_of_ordS {x : Ser} (h : ((0 : ℚ) : WithTop ℚ) ≤ ordS x) : IsIntegral x := by
  intro γ hγ
  have h1 : ((γ : ℚ) : WithTop ℚ) < ordS x := lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hγ) h
  exact (lt_ordS_iff _ γ).mp h1 γ le_rfl

/-- **Scaled traces of VF-bounded sets lie in `𝒪`** once `L` is large. -/
theorem rationalIntegral_strace (m : ℕ+) (B : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N))
    (hB : DiamondIntegral.Section6.VFBounded B.carrier) :
    ∃ N : ℕ, ∀ L, N ≤ L → RationalIntegral m (mixedSet (strace P L B)) := by
  obtain ⟨N, hN⟩ := vf_lower_bound P B hB
  refine ⟨N, fun L hL p hp _ i => ?_⟩
  rw [mem_mixedSet_scale] at hp
  have h1 := hN _ hp i
  intro γ hγ
  have he : p.1 i = tPow L * (tInv L * p.1 i) := (tPow_mul_tInv L _).symm
  rw [he]
  have h2 : ((γ : ℚ) : WithTop ℚ) < ordS (tPow L * (tInv L * p.1 i)) := by
    rw [lt_ordS_tPow_mul]
    refine lt_of_lt_of_le (WithTop.coe_lt_coe.mpr ?_) h1
    have : (N : ℚ) ≤ L := by exact_mod_cast hL
    linarith
  exact (lt_ordS_iff _ γ).mp h2 γ le_rfl

/-! ### Labels -/

/-- **Labels of concrete points of an RV-bounded set are bounded.** -/
theorem label_bounds (B : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N))
    (hB : DiamondIntegral.Section6.RVSupportDoublyBounded B.carrier) :
    ∃ q₁ q₂ : ℚ, ∀ p ∈ mixedSet (traceRaw P B), ∀ j,
      ((q₂ : ℚ) : WithTop ℚ) ≤ value (p.2 j) ∧ value (p.2 j) ≤ ((q₁ : ℚ) : WithTop ℚ) := by
  let Bc := (rawMixedSpace (M := P.N) n l).preimage B.carrier
  let Gup : Set (Fin 1 → P.N) := {y | iRV (y 0) ∧ y 0 ≠ iRVZero} ∩
    ⋂ j : Fin l, {y | ∀ w ∈ Bc, iLe ((fun v : Fin 1 ⊕ (Fin n ⊕ Fin l) → P.N => v (.inr (.inr j))) (Sum.elim y w))
      ((fun v : Fin 1 ⊕ (Fin n ⊕ Fin l) → P.N => v (.inl 0)) (Sum.elim y w))}
  let Glo : Set (Fin 1 → P.N) := {y | iRV (y 0) ∧ y 0 ≠ iRVZero} ∩
    ⋂ j : Fin l, {y | ∀ w ∈ Bc, iLe ((fun v : Fin 1 ⊕ (Fin n ⊕ Fin l) → P.N => v (.inl 0)) (Sum.elim y w))
      ((fun v : Fin 1 ⊕ (Fin n ⊕ Fin l) → P.N => v (.inr (.inr j))) (Sum.elim y w))}
  have hGup : (P.G.real : Set P.N).Definable LRV Gup :=
    nonzeroRV_definable.inter (Set.definable_iInter_of_finite fun j =>
      forall_le_definable B.definable (fun v => v (.inr (.inr j))) (fun v => v (.inl 0))
        (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV))
  have hGlo : (P.G.real : Set P.N).Definable LRV Glo :=
    nonzeroRV_definable.inter (Set.definable_iInter_of_finite fun j =>
      forall_le_definable B.definable (fun v => v (.inl 0)) (fun v => v (.inr (.inr j)))
        (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV))
  obtain ⟨γ, hγ⟩ := hB
  obtain ⟨a₁, ha₁, ha₁γ⟩ := SpecialTransformations.Section3.GammaParameters.EndpointLogic.codeValue_surjective γ
  obtain ⟨a₂, ha₂, ha₂γ⟩ := SpecialTransformations.Section3.GammaParameters.EndpointLogic.codeValue_surjective γ⁻¹
  have hneup : Gup.Nonempty := by
    refine ⟨fun _ => a₁, ⟨ha₁.1, ha₁.2⟩, Set.mem_iInter.mpr fun j => ?_⟩
    intro w hw
    obtain ⟨p, hp, rfl⟩ := decode_codes P B hw
    have h1 := (hγ p hp j).2
    rw [← ha₁γ, codeValue_val P ha₁] at h1
    exact (Values.vrv_le_iff _ _).mp h1
  have hnelo : Glo.Nonempty := by
    refine ⟨fun _ => a₂, ⟨ha₂.1, ha₂.2⟩, Set.mem_iInter.mpr fun j => ?_⟩
    intro w hw
    obtain ⟨p, hp, rfl⟩ := decode_codes P B hw
    have h1 := (hγ p hp j).1
    rw [← ha₂γ, codeValue_val P ha₂] at h1
    exact (Values.vrv_le_iff _ _).mp h1
  have hconc : ∀ c : Fin 1 → Carrier, iRV (P.e (c 0)) → P.e (c 0) ≠ iRVZero →
      ∃ u : RationalRVUnits ℂ, c 0 = Sum.inr (some u) := by
    intro c hrv hnz
    have hrv' : sortEval .rv (c 0) := (e_sort P .rv (c 0)).mp hrv
    obtain ⟨r, hr⟩ : ∃ r : RV, c 0 = Sum.inr r := by
      rcases hc0 : c 0 with f | r
      · rw [hc0] at hrv'
        exact absurd hrv' (fun h => h trivial)
      · exact ⟨r, rfl⟩
    have hrz : r ≠ none := by
      intro h
      apply hnz
      rw [hr, h, ← e_iRVZero]
      rfl
    obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.mp hrz
    exact ⟨u, hr⟩
  obtain ⟨c₁, ⟨hrv₁, hnz₁⟩, hall₁⟩ := concrete_witness P hGup hneup
  obtain ⟨c₂, ⟨hrv₂, hnz₂⟩, hall₂⟩ := concrete_witness P hGlo hnelo
  obtain ⟨u₁, hu₁⟩ := hconc c₁ hrv₁ hnz₁
  obtain ⟨u₂, hu₂⟩ := hconc c₂ hrv₂ hnz₂
  refine ⟨Multiplicative.toAdd u₁.1, Multiplicative.toAdd u₂.1, fun p hp j => ⟨?_, ?_⟩⟩
  · have h1 := (Set.mem_iInter.mp hall₂ j) _ (codes_mem P B p hp)
    change iLe (P.e (c₂ 0)) (P.e (Sum.inr (p.2 j))) at h1
    rw [e_iLe, hu₂] at h1
    exact (iLe_rvTag (some u₂) (p.2 j)).mp h1
  · have h1 := (Set.mem_iInter.mp hall₁ j) _ (codes_mem P B p hp)
    change iLe (P.e (Sum.inr (p.2 j))) (P.e (c₁ 0)) at h1
    rw [e_iLe, hu₁] at h1
    exact (iLe_rvTag (p.2 j) (some u₁)).mp h1

theorem labelsNonzero_strace (L : ℕ) (B : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N))
    (hB : DiamondIntegral.Section6.RVSupportDoublyBounded B.carrier) :
    LabelsNonzero (mixedSet (strace P L B)) := by
  obtain ⟨q₁, q₂, h⟩ := label_bounds P B hB
  intro p hp j hj
  rw [mem_mixedSet_scale] at hp
  have := (h _ hp j).2
  change value (p.2 j) ≤ _ at this
  rw [hj] at this
  change (⊤ : WithTop ℚ) ≤ _ at this
  exact absurd this (not_le.mpr (WithTop.coe_lt_top _))

/-- The label patterns with exponents between `a` and `c`. -/
def patternBox (a c : ℤ) : Finset (Fin l → ℤ) := Fintype.piFinset fun _ => Finset.Icc a c

theorem covers_strace (m : ℕ+) (L : ℕ) (B : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N))
    (hB : DiamondIntegral.Section6.RVSupportDoublyBounded B.carrier) :
    ∃ Q : Finset (Fin l → ℤ), Covers m Q (mixedSet (strace P L B)) := by
  obtain ⟨q₁, q₂, h⟩ := label_bounds P B hB
  refine ⟨patternBox ⌈(m : ℕ) * q₂⌉ ⌊(m : ℕ) * q₁⌋, fun p hp _ hu => ?_⟩
  rw [mem_mixedSet_scale] at hp
  have hm : (0 : ℚ) < ((m : ℕ) : ℚ) := by exact_mod_cast m.pos
  have hz : ∀ j, ∃ z : ℤ, z ∈ Finset.Icc ⌈(m : ℕ) * q₂⌉ ⌊(m : ℕ) * q₁⌋ ∧ p.2 j ∈ Line (zlev m z) := by
    intro j
    rcases hpj : p.2 j with _ | u
    · exact ⟨⌈(m : ℕ) * q₂⌉, Finset.mem_Icc.mpr ⟨le_rfl, by
        have h1 := h _ hp j
        change (_ : WithTop ℚ) ≤ value (p.2 j) ∧ value (p.2 j) ≤ _ at h1
        rw [hpj] at h1
        change _ ∧ (⊤ : WithTop ℚ) ≤ _ at h1
        exact absurd h1.2 (not_le.mpr (WithTop.coe_lt_top _))⟩, Or.inl rfl⟩
    · obtain ⟨z, hz⟩ := hu j u hpj
      have h1 := h _ hp j
      change (_ : WithTop ℚ) ≤ value (p.2 j) ∧ value (p.2 j) ≤ _ at h1
      rw [hpj] at h1
      change ((q₂ : ℚ) : WithTop ℚ) ≤ ((Multiplicative.toAdd u.1 : ℚ) : WithTop ℚ) ∧
        ((Multiplicative.toAdd u.1 : ℚ) : WithTop ℚ) ≤ ((q₁ : ℚ) : WithTop ℚ) at h1
      rw [WithTop.coe_le_coe, WithTop.coe_le_coe, hz] at h1
      refine ⟨z, Finset.mem_Icc.mpr ⟨?_, ?_⟩, Or.inr ⟨u.2, ?_⟩⟩
      · apply Int.ceil_le.mpr
        have := (le_div_iff₀ hm).mp h1.1
        linarith
      · apply Int.le_floor.mpr
        have := (div_le_iff₀ hm).mp h1.2
        linarith
      · rw [zlev, ← hz]
        rfl
  choose q hq using hz
  exact ⟨q, Fintype.mem_piFinset.mpr fun j => (hq j).1, fun j => (hq j).2⟩

/-! ### Invariance radii -/

variable (Gv : Type) [LinearOrderedCommGroupWithZero Gv] [Valued (VF P.N) Gv]
variable (hv : ∀ x y : VF P.N, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

/-- A named value of `Γ` is a rational power of `π`. -/
theorem named_rational {δ : Values.Gamma (M := P.N)}
    (h : (P.G.real : Set P.N).Definable LRV {z : Fin 1 → P.N | z 0 ∈ Values.gammaPullback {δ}}) :
    ∃ q : ℚ, δ = qpow π q :=
  PuiseuxValues.definable_point_rational P ((DiamondIntegral.Section6.gamma_real_codes_iff P.hc (P.G.real : Set P.N) {δ}).mpr h)

include hv in
/-- **A proper invariant set is invariant at the radii `π^{b_i/m − L}`** once these are large. -/
theorem amb_invariant (m : ℕ+) (B : DefSet (rawMixedSpace (M := P.N) n l) (P.G.real : Set P.N))
    (hB : DiamondIntegral.Section6.ProperInvariant (P.G.real : Set P.N) B.carrier) :
    ∃ q : ℚ, ∀ (L : ℕ) (b : Fin n → ℕ), (∀ i, q ≤ lev m (b i) - L) → AmbInvariant P (rad P m b L) B.carrier := by
  obtain ⟨δ, hδ, -, hinv⟩ := DiamondIntegral.Section6.properInvariant_uniform_named_radius P.G.model00 P.hc
    (DiamondIntegral.Section5.GammaQE.gamma_piecewise_rational_affine (M := P.N)) P.G.uncountable
    P.G.saturated hv P.G.small_real (Hm.base_nontrivial P) hB
  obtain ⟨q, rfl⟩ := named_rational P hδ
  refine ⟨q, fun L b hb a ha x hx => ?_⟩
  have hc : DiamondIntegral.Section6.Congruent (fun _ => qpow π q) a.1 x := by
    intro i
    refine lt_of_le_of_lt ?_ (hx i)
    change (qpow π q).val ≤ (qpow π (lev m (b i) - L)).val
    exact (Hm.qpow_le_iff P).mpr (hb i)
  have := ((hinv a.2) a.1 x hc).mp ha
  exact this

end DiamondIntegral.Section8.Truncation
