import «section 8».LiftTrunc

/-! **The truncation class of a lift** (the computation in the proof of Lemma `inv:dir:com`).

For a doubly bounded measured RV object `U` with form `1` and `m ≥ 1`, at every large scale `L` and
cutoffs `b`, the normalized class of the truncation of `t^L 𝕃U` is `η h_m [U] · 𝕃^{-mnL}`
(`lift_class`). The finitely many value patterns come from a rational bound of the concrete values of
`U` (`rv_bounds`, by elementarity). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.Hm DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.GammaCells

local instance liftClassStructure : LRV.Structure Carrier := canonicalInterpret
local instance liftClassModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

variable (P : PuiseuxAmbient)

theorem rawRV_decode_P {K : ℕ} (x : Fin K → CanonicalRV.RVSort P.N) :
    (rawRVSpace (M := P.N) K).decode ⟨rvValues x, ⟨x, rfl⟩⟩ = x :=
  rvValues_injective (Classical.choose_spec (⟨x, rfl⟩ : rvValues x ∈ Set.range (rvValues (M := P.N))))

/-- **Concrete points of a doubly bounded RV set have bounded values.** -/
theorem rv_bounds {K : ℕ} (R : Set (Fin K → CanonicalRV.RVSort P.N))
    (hR : (rawRVSpace (M := P.N) K).Definable (P.G.real : Set P.N) R)
    (hb : DiamondIntegral.Section2.RVValueDoublyBounded R) :
    ∃ q₁ q₂ : ℚ, ∀ s : Fin K → RV, eRVs P s ∈ R → ∀ i,
      ((q₂ : ℚ) : WithTop ℚ) ≤ value (s i) ∧ value (s i) ≤ ((q₁ : ℚ) : WithTop ℚ) := by
  let Rc := (rawRVSpace (M := P.N) K).preimage R
  have hRc : (P.G.real : Set P.N).Definable LRV Rc := hR
  let Gup : Set (Fin 1 → P.N) := {y | iRV (y 0) ∧ y 0 ≠ iRVZero} ∩
    ⋂ j : Fin K, {y | ∀ w ∈ Rc, iLe ((fun v : Fin 1 ⊕ Fin K → P.N => v (.inr j)) (Sum.elim y w))
      ((fun v : Fin 1 ⊕ Fin K → P.N => v (.inl 0)) (Sum.elim y w))}
  let Glo : Set (Fin 1 → P.N) := {y | iRV (y 0) ∧ y 0 ≠ iRVZero} ∩
    ⋂ j : Fin K, {y | ∀ w ∈ Rc, iLe ((fun v : Fin 1 ⊕ Fin K → P.N => v (.inl 0)) (Sum.elim y w))
      ((fun v : Fin 1 ⊕ Fin K → P.N => v (.inr j)) (Sum.elim y w))}
  have hGup : (P.G.real : Set P.N).Definable LRV Gup :=
    nonzeroRV_definable.inter (Set.definable_iInter_of_finite fun j =>
      forall_le_definable hRc (fun v => v (.inr j)) (fun v => v (.inl 0))
        (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV))
  have hGlo : (P.G.real : Set P.N).Definable LRV Glo :=
    nonzeroRV_definable.inter (Set.definable_iInter_of_finite fun j =>
      forall_le_definable hRc (fun v => v (.inl 0)) (fun v => v (.inr j))
        (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV))
  obtain ⟨γ, hγ⟩ := hb
  obtain ⟨a₁, ha₁, ha₁γ⟩ := SpecialTransformations.Section3.GammaParameters.EndpointLogic.codeValue_surjective γ
  obtain ⟨a₂, ha₂, ha₂γ⟩ := SpecialTransformations.Section3.GammaParameters.EndpointLogic.codeValue_surjective γ⁻¹
  have hdec : ∀ w ∈ Rc, ∃ u ∈ R, rvValues u = w := by
    rintro w ⟨hw, hR'⟩
    exact ⟨_, hR', Classical.choose_spec hw⟩
  have hneup : Gup.Nonempty := by
    refine ⟨fun _ => a₁, ⟨ha₁.1, ha₁.2⟩, Set.mem_iInter.mpr fun j => ?_⟩
    intro w hw
    obtain ⟨u, hu, rfl⟩ := hdec w hw
    have h1 := (hγ u hu j).2
    rw [← ha₁γ, codeValue_val P ha₁] at h1
    exact (Values.vrv_le_iff _ _).mp h1
  have hnelo : Glo.Nonempty := by
    refine ⟨fun _ => a₂, ⟨ha₂.1, ha₂.2⟩, Set.mem_iInter.mpr fun j => ?_⟩
    intro w hw
    obtain ⟨u, hu, rfl⟩ := hdec w hw
    have h1 := (hγ u hu j).1
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
  have hmem : ∀ s : Fin K → RV, eRVs P s ∈ R → rvValues (eRVs P s) ∈ Rc := fun s hs =>
    ⟨⟨eRVs P s, rfl⟩, by rw [rawRV_decode_P]; exact hs⟩
  refine ⟨Multiplicative.toAdd u₁.1, Multiplicative.toAdd u₂.1, fun s hs i => ⟨?_, ?_⟩⟩
  · have h1 := (Set.mem_iInter.mp hall₂ i) _ (hmem s hs)
    change iLe (P.e (c₂ 0)) (P.e (Sum.inr (s i))) at h1
    rw [e_iLe, hu₂] at h1
    exact (iLe_rvTag (some u₂) (s i)).mp h1
  · have h1 := (Set.mem_iInter.mp hall₁ i) _ (hmem s hs)
    change iLe (P.e (Sum.inr (s i))) (P.e (c₁ 0)) at h1
    rw [e_iLe, hu₁] at h1
    exact (iLe_rvTag (s i) (some u₁)).mp h1

variable {n : ℕ} (U : DiamondIntegral.Section6.MeasuredRVObject (M := P.N) (P.G.real : Set P.N) n)

open DiamondIntegral.Section7.ChartOfMeasured

/-- **Finitely many value patterns.** -/
theorem value_patterns (hU : U.doublyBounded) (m : ℕ+) :
    ∃ a c : ℤ, ∀ (t : Fin U.object.arity → RV) (ht : eRVs P t ∈ U.object.domain.carrier),
      (∀ j, LabelRational m (t j)) → ∃ z ∈ (patternBox a c : Finset (Fin n → ℤ)),
        ∀ i, rvq (fcv P U t ht i) = (z i : ℚ) / (m : ℕ) := by
  have hR := U.object.volume.definable_image
  obtain ⟨q₁, q₂, hq⟩ := rv_bounds P _ hR hU.2
  have hm : (0 : ℚ) < ((m : ℕ) : ℚ) := by exact_mod_cast m.pos
  refine ⟨⌈((m : ℕ) : ℚ) * q₂⌉, ⌊((m : ℕ) : ℚ) * q₁⌋, fun t ht hrat => ?_⟩
  have hfr := concrete_rv_image_rational P U.object.volume m t ht (fcv P U t ht) (fcv_spec P U t ht) hrat
  have hmem : eRVs P (fcv P U t ht) ∈ Set.range (fun a => (U.object.volume a).val) :=
    ⟨⟨eRVs P t, ht⟩, fcv_spec P U t ht⟩
  have hex : ∀ i, ∃ z : ℤ, z ∈ Finset.Icc ⌈((m : ℕ) : ℚ) * q₂⌉ ⌊((m : ℕ) : ℚ) * q₁⌋ ∧
      rvq (fcv P U t ht i) = (z : ℚ) / (m : ℕ) := by
    intro i
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp (fcv_ne_none P U t ht i)
    obtain ⟨z, hz⟩ := hfr i u hu
    have hb := hq _ hmem i
    rw [hu] at hb
    change ((q₂ : ℚ) : WithTop ℚ) ≤ ((Multiplicative.toAdd u.1 : ℚ) : WithTop ℚ) ∧
      ((Multiplicative.toAdd u.1 : ℚ) : WithTop ℚ) ≤ ((q₁ : ℚ) : WithTop ℚ) at hb
    rw [WithTop.coe_le_coe, WithTop.coe_le_coe, hz] at hb
    refine ⟨z, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · apply Int.ceil_le.mpr
      have := (le_div_iff₀ hm).mp hb.1
      linarith
    · apply Int.le_floor.mpr
      have := (div_le_iff₀ hm).mp hb.2
      linarith
    · rw [hu]
      exact hz
  choose z hz using hex
  exact ⟨z, Fintype.mem_piFinset.mpr fun i => (hz i).1, fun i => (hz i).2⟩

/-- **The truncation class of a lift.** For a doubly bounded measured RV object `U` with form `1`,
at large scales `L` and cutoffs `b`, `[(t^L 𝕃U)[m;b/m]] 𝕃^{-Σb} = η h_m [U] · 𝕃^{-mnL}`. -/
theorem lift_class (hU : U.doublyBounded)
    (hform : ∀ u, DiamondIntegral.Section6.gammaMapValue U.form u = 1) (m : ℕ+) :
    ∃ L0 b0 : ℕ, ∀ L, L0 ≤ L → ∀ b : Fin n → ℕ, (∀ i, b0 + (m : ℕ) * L ≤ b i) →
      ∀ (Q : Finset (Fin U.object.arity → ℤ))
        (hA : Invariant m b (mixedSet (strace P L (SpecialTransformations.Section4.rvLift U.object))))
        (hQ : Covers m Q (mixedSet (strace P L (SpecialTransformations.Section4.rvLift U.object)))),
        fullClass m b Q (strace_definableOver P L _) hA hQ =
          zetaCoeff P (RVBoundedRing.objectClass (objOf P.hc P.G.real U hU)) m * Linv (n * ((m : ℕ) * L)) := by
  obtain ⟨a, c, hpat⟩ := value_patterns P U hU m
  refine ⟨a.natAbs, c.toNat, fun L hL b hb Q hA hQ => ?_⟩
  obtain ⟨D, hDf, hD, hz⟩ := zetaCoeff_U P U hU hform m (patternBox a c) hpat
  have hbox : ∀ z ∈ (patternBox a c : Finset (Fin n → ℤ)), ∀ i, a ≤ z i ∧ z i ≤ c := fun z hz i =>
    Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hz i)
  have hm1 : (1 : ℤ) ≤ (m : ℕ) := by exact_mod_cast m.pos
  have hz0 : ∀ z ∈ (patternBox a c : Finset (Fin n → ℤ)), ∀ i, 0 ≤ z i + (m : ℕ) * L := by
    intro z hz' i
    have h1 := (hbox z hz' i).1
    have h2 : (a.natAbs : ℤ) ≤ L := by exact_mod_cast hL
    have h3 : -(a.natAbs : ℤ) ≤ a := by omega
    nlinarith
  have hzb : ∀ z ∈ (patternBox a c : Finset (Fin n → ℤ)), ∀ i, lead m L z i ≤ b i := by
    intro z hz' i
    have h1 := (hbox z hz' i).2
    have h2 := hb i
    unfold lead
    have h3 : c ≤ (c.toNat : ℤ) := Int.self_le_toNat c
    omega
  rw [fullClass_lift P U m L b hform Q hA hQ hU (patternBox a c) hpat D hDf hD hz0 hzb, hz]

end DiamondIntegral.Section8.Truncation
