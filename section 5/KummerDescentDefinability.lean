import «section 5».KummerRootDefinability
import «section 5».ComplexResidueDefinability
import Section4.CodeMaps

/-! The inverse finite-level construction is definable over the original
Laurent base. Its root is an existential variable in a definable source,
and its coordinate map consists of original RV monomials. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section3
local instance descentDefinabilityStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem rvTag_some_zpow (u : RationalRVUnits ℂ) (j : ℤ) :
    rvTag (some u) ^ j = rvTag (some (u ^ j)) :=
  (map_zpow rvUnitTagHom u j).symm

theorem rootFrame_tag (N : ℕ+) (r : KummerRVRoot N) (a : ℤ) (c : ℂ) :
    rvTag (some r.val) ^ a * rvTag (residueLift c) =
      rvTag (linePoint ((a : ℚ) / (N : ℕ)) (((r.val.2 ^ a : ℂˣ) : ℂ) * c)) := by
  rw [rvTag_some_zpow, ← rvTag_mul]
  apply congrArg rvTag
  have hq : (r.val ^ a).1 = Multiplicative.ofAdd ((a : ℚ) / (N : ℕ)) := by
    change r.val.1 ^ a = _
    rw [kummerRVRoot_value]
    change Multiplicative.ofAdd (a • ((1 : ℚ) / (N : ℕ))) = _
    congr 1
    simp [zsmul_eq_mul, div_eq_mul_inv]
  by_cases hc : c = 0
  · simp [residueLift, hc, rvMul, linePoint]
  · simp only [residueLift, hc, ↓reduceDIte, rvMul, linePoint,
      mul_ne_zero (Units.ne_zero _) hc]
    congr 1
    apply Prod.ext
    · exact (mul_one _).trans hq
    · exact Units.ext rfl

def descentSource {n : ℕ} (N : ℕ+) (X : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) :
    DefSet (rawRVSpace (M := Carrier) (n + 1)) {c | baseCarrier c} where
  carrier := {u | (fun _ : Fin 1 => (u 0).val) ∈
      (rawRVSpace 1).preimage (originalKummerRoots N).carrier ∧
    rvValues (u ∘ Fin.succ) ∈ complexResidueImage X}
  definable := by
    have hr := (originalKummerRoots N).definable.preimage_comp (fun _ : Fin 1 => (0 : Fin (n + 1)))
    have hx := (complex_residue_image_definable X hX).preimage_comp (Fin.succ : Fin n → Fin (n + 1))
    have hd := ((rawRVSpace (M := Carrier) (n + 1)).definable_domain {c | baseCarrier c}).inter
      (hr.inter hx)
    change {c | baseCarrier c}.Definable LRV _
    convert hd using 1
    ext z
    constructor
    · rintro ⟨hz, hu⟩
      have he := rvValues_decode (⟨z, hz⟩ : (rawRVSpace (M := Carrier) (n + 1)).domain)
      change ((fun _ : Fin 1 => rvValues ((rawRVSpace (n + 1)).decode ⟨z, hz⟩) 0) ∈ _ ∧
        (rvValues ((rawRVSpace (n + 1)).decode ⟨z, hz⟩) ∘ Fin.succ) ∈ _) at hu
      rw [he] at hu
      exact ⟨hz, hu⟩
    · rintro ⟨hz, hu⟩
      refine ⟨hz, ?_⟩
      have he := rvValues_decode (⟨z, hz⟩ : (rawRVSpace (M := Carrier) (n + 1)).domain)
      change (fun _ : Fin 1 => rvValues ((rawRVSpace (n + 1)).decode ⟨z, hz⟩) 0) ∈ _ ∧
        (rvValues ((rawRVSpace (n + 1)).decode ⟨z, hz⟩) ∘ Fin.succ) ∈ _
      rwa [he]

def descentExponents {n : ℕ} (a : Fin n → ℤ) (i : Fin n) : Fin (n + 1) → ℤ :=
  Fin.cons (a i) (fun j => if j = i then 1 else 0)

theorem descentMonomial_value {n : ℕ} (a : Fin n → ℤ)
    (u : Fin (n + 1) → CanonicalRV.RVSort Carrier) (i : Fin n) :
    (∏ j, u j ^ descentExponents a i j) = u 0 ^ a i * u i.succ := by
  simp only [Fin.prod_univ_succ, descentExponents, Fin.cons_zero, Fin.cons_succ]
  simp_rw [pow_ite, zpow_one, zpow_zero]
  simp

def descentMonomialMap {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) (X : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) :
    Map (descentSource N X hX) (DefSet.univ (rawRVSpace (M := Carrier) n) {c | baseCarrier c}) := by
  let f (u : Fin (n + 1) → CanonicalRV.RVSort Carrier) : Fin n → CanonicalRV.RVSort Carrier :=
    fun i => ∏ j, u j ^ descentExponents a i j
  let F (z : Fin (n + 1) → Carrier) : Fin n → Carrier :=
    fun i => (rvIntegerMonomialTerm (descentExponents a i)).realize z
  have hF : {c | baseCarrier c}.DefinableMap LRV F :=
    fun i => Set.DefinableFun.of_empty (rvIntegerMonomialTerm (descentExponents a i)).definableFun_realize
  have he (c : (rawRVSpace (M := Carrier) (n + 1)).domain) :
      F c.val = rvValues (f ((rawRVSpace (n + 1)).decode c)) := by
    funext i
    have h := rvIntegerMonomialTerm_realize (descentExponents a i) ((rawRVSpace (n + 1)).decode c)
    rw [rvValues_decode] at h
    exact h
  have hdom (c : (rawRVSpace (M := Carrier) (n + 1)).domain) :
      F c.val ∈ (rawRVSpace (M := Carrier) n).domain := ⟨_, (he c).symm⟩
  refine Map.ofCodes (descentSource N X hX) f F hF hdom ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode _).trans (he c)

theorem descentMonomialMap_range {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) (X : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) :
    Set.range (fun u : descentSource N X hX => (descentMonomialMap N a X hX u).val) =
      {v | ∃ r : KummerRVRoot N, ∃ x ∈ X, v = fun i => rvTag (frameAtRoot N a r x i)} := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    let r' : originalKummerRoots N :=
      ⟨fun _ => u.val 0, (rawRV_preimage_mem _ _).mp u.property.1⟩
    obtain ⟨r, hr⟩ := (originalKummerRootEquiv N).surjective r'
    have hroot : u.val 0 = rvTag (some r.val) :=
      (congrArg (fun t : originalKummerRoots N => t.val 0) hr).symm
    obtain ⟨x, hx, hcoords⟩ := u.property.2
    refine ⟨r, x, hx, ?_⟩
    funext i
    change (∏ j, u.val j ^ descentExponents a i j) = _
    rw [descentMonomial_value, hroot]
    have hc : u.val i.succ = rvTag (residueLift (x i)) :=
      Subtype.ext (congrFun hcoords i).symm
    rw [hc, rootFrame_tag]
    rfl
  · rintro ⟨r, x, hx, rfl⟩
    let u : Fin (n + 1) → CanonicalRV.RVSort Carrier :=
      Fin.cons (rvTag (some r.val)) (fun i => rvTag (residueLift (x i)))
    have hu : u ∈ (descentSource N X hX).carrier := by
      constructor
      · apply (rawRV_preimage_mem _ _).mpr
        exact (originalKummerRootMap N r).property
      · exact ⟨x, hx, rfl⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    funext i
    change (∏ j, u j ^ descentExponents a i j) = _
    rw [descentMonomial_value]
    exact rootFrame_tag N r (a i) (x i)

def descendedOriginalSet {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) (X : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) :
    DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c} :=
  ⟨Set.range (fun u : descentSource N X hX => (descentMonomialMap N a X hX u).val),
    (descentMonomialMap N a X hX).definable_image⟩

end DiamondIntegral.Section5.PuiseuxOriginal
