import «section 8».SameType
import «section 8».VolComparison
import «section 8».MilnorSmoothJets

/-! Remark 8.15 (`rem-comp-milnor-fib-bis`): `∫[𝒳_f] = [1] ∫[𝒳_t]` and `Vol([𝒳_f]) = Vol([𝒳_t])`.

Setting: `X ⊆ 𝔸^d` cut out by `g = 0` near the origin, `X(𝔪) = {x ∈ 𝔪^d | g(x) = 0}` (`tube`),
`f ∈ ℂ[x]`, `𝒳_y = {x ∈ X(𝔪) | f(x) = y}` (`fiberSet`), so `𝒳_f = ⋃_{rv(y) = rv(t)} 𝒳_y`
(`sourceSet`). `X = 𝔸^d` is `g = ∅` (`remark_8_15_affine`); for smooth affine `X` the étale chart
identifies `𝒳_f ⊆ X(𝔪)` with the Milnor fiber in chart coordinates (`remark_8_15_smooth`).

The argument is the manuscript's.
1. Let `𝕊₀` be the parameter set `ℂ ∪ {t}` (`S0`). By the preparation theorem
   (`native_arbitrary_vf_pullback_preparation`, valid over any small base) there is a bijection
   `F_t : 𝒳_t → Y`, definable over `𝕊₀`, onto an RV-pullback `Y` (the manuscript writes `Y = 𝕃U`;
   only the pullback property is used).
2. Moving `t` into a variable (`definable_extract_param`), the graph of `F_t`, and the RV set of which
   `Y` is the pullback, are fibres at `t` of families definable over `ℂ`. The set of `y` over which
   the fibre of the graph family is the graph of a bijection `𝒳_y → Y_y` is definable over `ℂ`
   (`bijGraph_definable`) and contains `t` (`Good_t`).
3. Every `t'` with `rv(t') = rv(t)` has the same type as `t` over `ℂ ∪ RV` (`same_type_sum`, by
   quantifier elimination); so the fibre at `t'` is a bijection `F_{t'} : 𝒳_{t'} → Y_{t'} = Y`
   (`bij_t'`).
4. `x ↦ (f(x), 1, F_{f(x)}(x))` is a bijection from `𝒳_f` onto `(rv(t)^♯ × {1}) × Y`, definable over
   the base of Section 8 (`PhiMap`, `PhiMap_bijective`).

Hence `[𝒳_f] = [rv(t)^♯ × {1}] [Y] = [rv(t)^♯ × {1}] [𝒳_t]` (`remark_8_15_class`); `∫` of the lift
`rv(t)^♯ × {1}` is the class `[1]` of a point (`integral_RObj`), and `E_b([1]) = 1`
(`nativeRVEvaluation_point`). No cited input beyond those of `𝒳_f` itself (the étale chart for
smooth `X`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section9 SpecialTransformations.Section4
open DiamondIntegral.Section2 DiamondIntegral.Section3 DiamondIntegral.Section6
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.Milnor DiamondIntegral.Section8.SameType
open DiamondIntegral.Section4 DiamondIntegral.Section7

namespace DiamondIntegral.Section8.Remark815

variable (P : PuiseuxAmbient) {d k : ℕ} (g : Fin k → MvPolynomial (Fin d) ℂ) (f : MvPolynomial (Fin d) ℂ)

/-! ### The parameter sets `ℂ` and `𝕊₀ = ℂ ∪ {t}` -/

/-- The image of `ℂ`. -/
def CC : Set P.N := Set.range fun c : ℂ => (ambientComplexFieldHom P.e c).val

/-- The image of `ℂ` as a subfield. -/
def EE : Subfield (VFType (M := P.N)) := (ambientComplexFieldHom P.e).fieldRange

theorem EE_value : ∀ e ∈ EE P, e ≠ 0 → Values.vfValueHom e = 1 := by
  rintro e ⟨c, rfl⟩ he
  exact complex_value P c (fun h => he (by rw [h, map_zero]))

theorem CC_mem : ∀ c ∈ CC P, ∀ h : iVF c, (⟨c, h⟩ : VFType (M := P.N)) ∈ EE P := by
  rintro _ ⟨c, rfl⟩ h
  exact ⟨c, Subtype.ext rfl⟩

theorem CC_complex (c : ℂ) : (ambientComplexFieldHom P.e c).val ∈ CC P := ⟨c, rfl⟩

theorem CC_zero : (0 : VFType (M := P.N)).val ∈ CC P := ⟨0, congrArg Subtype.val (ambientComplexFieldHom P.e).map_zero⟩

theorem CC_one : (1 : VFType (M := P.N)).val ∈ CC P := ⟨1, congrArg Subtype.val (ambientComplexFieldHom P.e).map_one⟩

theorem CC_coeff (c : Fin d →₀ ℕ) : ((fN P f).coeff c).val ∈ CC P := by
  rw [MvPolynomial.coeff_map]
  exact CC_complex P _

/-- `𝕊₀`: the image of `ℂ` and `t`. -/
def S0 : Set P.N := insert (tN P).val (CC P)

theorem CC_sub_S0 : CC P ⊆ S0 P := Set.subset_insert _ _

theorem tN_mem_S0 : (tN P).val ∈ S0 P := Set.mem_insert _ _

theorem CC_sub_real : CC P ⊆ (P.G.real : Set P.N) := by
  rintro _ ⟨c, rfl⟩
  exact ambientComplexFieldHom_base_mem P.e P.G P.hB c

theorem S0_sub_real : S0 P ⊆ (P.G.real : Set P.N) :=
  Set.insert_subset (tN_mem P) (CC_sub_real P)

theorem S0_small : Cardinal.mk (S0 P) < P.G.κ :=
  (Cardinal.mk_le_mk_of_subset (S0_sub_real P)).trans_lt P.G.small_real

/-- The base `⟨𝕊₀, ∅⟩`. -/
abbrev B0 : Base (M := P.N) := ⟨S0 P, ∅⟩

/-! ### The family `𝒳_y` -/

/-- `𝒳_y = {x ∈ X(𝔪) | f(x) = y}`, with `X(𝔪) = {x ∈ 𝔪^d | g(x) = 0}` (`tube`). -/
def fiberSet (y : VFType (M := P.N)) : Set (Mixed P.N d 0) :=
  {p | p.1 ∈ tube P g ∧ MvPolynomial.eval p.1 (fN P f) = y}

/-- The codes of the family `(y, x)`, `x ∈ 𝒳_y`. -/
def famCodes : Set (Unit ⊕ (Fin d ⊕ Fin 0) → P.N) :=
  {w | (∀ i, w (.inr (.inl i)) ∈ SpecialTransformations.Section8.rawOpenBall (0 : VFType (M := P.N)).val
      (1 : VFType (M := P.N)).val) ∧
    (∀ j, SpecialTransformations.Section5.mvPolynomialCode (fN P (g j)) (w ∘ Sum.inr) = (0 : VFType (M := P.N)).val) ∧
    SpecialTransformations.Section5.mvPolynomialCode (fN P f) (w ∘ Sum.inr) = w (.inl ())}

omit f in
/-- A polynomial code in the family variables is definable over `ℂ`. -/
theorem famCode_definableFun (h : MvPolynomial (Fin d) ℂ) :
    (CC P).DefinableFun LRV (fun w : Unit ⊕ (Fin d ⊕ Fin 0) → P.N =>
      SpecialTransformations.Section5.mvPolynomialCode (fN P h) (w ∘ Sum.inr)) := by
  have hp := SpecialTransformations.Section5.mvPolynomialCode_definable (m := 0) (S := CC P)
    (fN P h) (CC_coeff P h)
  change @Set.DefinableFun P.N LRV (CanonicalStructure.normalize (M := P.N)) (Fin d ⊕ Fin 0)
    (CC P) (SpecialTransformations.Section5.mvPolynomialCode (m := 0) (fN P h)) at hp
  rw [SpecialTransformations.Section4.canonical_normalize_eq P.hc] at hp
  exact hp.comp (fun _ => Set.DefinableFun.proj LRV)

theorem famCodes_definable : (CC P).Definable LRV (famCodes P g f) := by
  have hball : (CC P).Definable LRV {w : Unit ⊕ (Fin d ⊕ Fin 0) → P.N | ∀ i, w (.inr (.inl i)) ∈
      SpecialTransformations.Section8.rawOpenBall (0 : VFType (M := P.N)).val (1 : VFType (M := P.N)).val} := by
    have heach (i : Fin d) := (SpecialTransformations.Section8.rawOpenBall_definable (CC_zero P)
      (CC_one P)).preimage_comp (fun _ : Fin 1 => (Sum.inr (Sum.inl i) : Unit ⊕ (Fin d ⊕ Fin 0)))
    convert Set.definable_iInter_of_finite heach using 1
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  have hzero : (CC P).Definable LRV {w : Unit ⊕ (Fin d ⊕ Fin 0) → P.N | ∀ j,
      SpecialTransformations.Section5.mvPolynomialCode (fN P (g j)) (w ∘ Sum.inr) = (0 : VFType (M := P.N)).val} := by
    convert Set.definable_iInter_of_finite (fun j => (famCode_definableFun P (g j)).ofPred_eq
      (LRV.definableFun_const _ (CC_zero P))) using 1
    ext w
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  convert hball.inter (hzero.inter ((famCode_definableFun P f).ofPred_eq
    (Set.DefinableFun.proj LRV (i := Sum.inl ())))) using 1
  ext w
  simp only [famCodes, Set.mem_inter_iff, Set.mem_ofPred_eq]

theorem mem_famCodes (y : VFType (M := P.N)) (p : Mixed P.N d 0) :
    Sum.elim (fun _ => y.val) (mixedValues p) ∈ famCodes P g f ↔ p ∈ fiberSet P g f y := by
  have hcode (h : MvPolynomial (Fin d) ℂ) :=
    SpecialTransformations.Section5.mvPolynomialCode_eq (fN P h) (mixedValues p) p.1 (fun i => rfl)
  simp only [famCodes, fiberSet, tube, Set.mem_ofPred_eq, Sum.elim_comp_inr, Sum.elim_inr, Sum.elim_inl, hcode]
  constructor
  · rintro ⟨hb, hz, he⟩
    exact ⟨⟨fun i => (mem_ball_iff P (p.1 i)).mp (hb i), fun j => Subtype.ext (hz j)⟩, Subtype.ext he⟩
  · rintro ⟨⟨hb, hz⟩, he⟩
    exact ⟨fun i => (mem_ball_iff P (p.1 i)).mpr (hb i), fun j => congrArg Subtype.val (hz j),
      congrArg Subtype.val he⟩

/-- Codes in the family lie in the domain of `rawMixedSpace d 0`. -/
theorem famCodes_domain {y : P.N} {z : Fin d ⊕ Fin 0 → P.N} (h : Sum.elim (fun _ => y) z ∈ famCodes P g f) :
    z ∈ (rawMixedSpace (M := P.N) d 0).domain := by
  have hvf : ∀ i, iVF (z (.inl i)) := by
    intro i
    have hb := h.1 i
    change z (.inl i) ∈ OpenBallCodes.rawBall ![(0 : VFType (M := P.N)).val, (1 : VFType (M := P.N)).val] at hb
    rw [OpenBallCodes.rawBall, Set.mem_ofPred_eq, OpenBallCodes.body_realize] at hb
    exact hb.2.1
  refine ⟨⟨fun i => ⟨z (.inl i), hvf i⟩, rfl⟩, ⟨Fin.elim0, funext fun i => i.elim0⟩⟩

/-! ### Codes of points -/

theorem mem_preimage_iff {n r : ℕ} (A : Set (Mixed P.N n r)) (z : Fin n ⊕ Fin r → P.N) :
    z ∈ (rawMixedSpace (M := P.N) n r).preimage A ↔ ∃ p ∈ A, mixedValues p = z := by
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨_, h, mixedValues_decode ⟨z, hz⟩⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨mixedValues_mem_domain p, by simpa only [decode_mixedValues] using hp⟩

theorem mem_prod_preimage_iff {n r n' r' : ℕ} (Γ : Set (Mixed P.N n r × Mixed P.N n' r'))
    (x : Fin n ⊕ Fin r → P.N) (z : Fin n' ⊕ Fin r' → P.N) :
    (Sum.elim x z : (Fin n ⊕ Fin r) ⊕ (Fin n' ⊕ Fin r') → P.N) ∈
        ((rawMixedSpace (M := P.N) n r).prod (rawMixedSpace (M := P.N) n' r')).preimage Γ ↔
      ∃ p w, (p, w) ∈ Γ ∧ mixedValues p = x ∧ mixedValues w = z := by
  constructor
  · rintro ⟨⟨hx, hz⟩, h⟩
    exact ⟨_, _, h, mixedValues_decode ⟨x, hx⟩, mixedValues_decode ⟨z, hz⟩⟩
  · rintro ⟨p, w, hΓ, rfl, rfl⟩
    refine ⟨⟨mixedValues_mem_domain p, mixedValues_mem_domain w⟩, ?_⟩
    show ((rawMixedSpace (M := P.N) n r).decode ⟨mixedValues p, mixedValues_mem_domain p⟩,
      (rawMixedSpace (M := P.N) n' r').decode ⟨mixedValues w, mixedValues_mem_domain w⟩) ∈ Γ
    rw [decode_mixedValues, decode_mixedValues]
    exact hΓ

/-- Replace the field-sort coordinates of a code by their `rv`. -/
def rvify {n r : ℕ} (z : Fin n ⊕ Fin r → P.N) : Fin n ⊕ Fin r → P.N :=
  Sum.elim (fun i => iRv (z (.inl i))) (fun j => z (.inr j))

theorem rv_coord_definableFun (S : Set P.N) {ι : Type} [Finite ι] (k : ι) :
    S.DefinableFun LRV (fun w : ι → P.N => iRv (w k)) :=
  (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := P.N) (L := LRV) Fn.rvMap)).comp
    (show S.DefinableMap LRV (fun w : ι → P.N => ![w k]) from by
      intro m
      fin_cases m
      exact Set.DefinableFun.proj LRV)

theorem rvify_definableMap (S : Set P.N) {ι : Type} [Finite ι] {n r : ℕ} (g : Fin n ⊕ Fin r → ι) :
    S.DefinableMap LRV (fun w : ι → P.N => rvify P (w ∘ g)) := by
  intro k
  rcases k with i | j
  · exact rv_coord_definableFun P S (g (.inl i))
  · exact Set.DefinableFun.proj LRV

/-! ### The fibre `𝒳_t` over `𝕊₀` -/

theorem fiberSet_t_definable :
    (rawMixedSpace (M := P.N) d 0).Definable (S0 P) (fiberSet P g f (tN P)) := by
  have hmap : (S0 P).DefinableMap LRV
      (fun z : Fin d ⊕ Fin 0 → P.N => (Sum.elim (fun _ : Unit => (tN P).val) z : Unit ⊕ (Fin d ⊕ Fin 0) → P.N)) := by
    intro k
    rcases k with _ | i
    · exact LRV.definableFun_const _ (tN_mem_S0 P)
    · exact Set.DefinableFun.proj LRV
  have h := ((famCodes_definable P g f).mono (CC_sub_S0 P)).preimage_map hmap
  convert mixedValues_preimage_definable _ h using 1
  ext p
  exact (mem_famCodes P g f (tN P) p).symm

/-- `𝒳_t` over `⟨𝕊₀, ∅⟩`. -/
def At : GammaGroundDefSet P.hc (B0 P) (rawMixedSpace (M := P.N) d 0) :=
  ⟨fiberSet P g f (tN P), GammaGroundDefinable.of_real (fiberSet_t_definable P g f)⟩

theorem one_lt_tN : 1 < Values.vfValueHom (tN P) := by
  rw [value_tN]
  exact one_lt_uniformizerValue P

/-! ### The prepared bijection `F_t : 𝒳_t → Y` and its codes -/

section Data

variable {l : ℕ} (Y : GammaGroundDefSet P.hc (B0 P) (rawMixedSpace (M := P.N) d l))
  (F : GammaGroundBijection (At P g f) Y)

/-- The codes of `Y`. -/
def Ycode : Set (Fin d ⊕ Fin l → P.N) := (rawMixedSpace (M := P.N) d l).preimage Y.carrier

omit g f in
theorem Ycode_definable : (S0 P).Definable LRV (Ycode P Y) :=
  gammaGround_empty_definable Y.definable

/-- The graph of `F_t`. -/
def graphSet : Set (Mixed P.N d 0 × Mixed P.N d l) :=
  {z | ∃ a : At P g f, a.val = z.1 ∧ (F.map.toFun a).val = z.2}

/-- The codes of the graph of `F_t`. -/
def Gcode : Set ((Fin d ⊕ Fin 0) ⊕ (Fin d ⊕ Fin l) → P.N) :=
  ((rawMixedSpace (M := P.N) d 0).prod (rawMixedSpace (M := P.N) d l)).preimage (graphSet P g f Y F)

theorem Gcode_definable : (S0 P).Definable LRV (Gcode P g f Y F) :=
  gammaGround_empty_definable F.map.graph_definable

/-- The RV set of which `Y` is the pullback (when it is one). -/
def Ybar : Set (Fin d ⊕ Fin l → P.N) := {w | ∃ z ∈ Ycode P Y, rvify P z = w}

omit g f in
theorem Ybar_definable : (S0 P).Definable LRV (Ybar P Y) := by
  have hT : (S0 P).Definable LRV {c : (Fin d ⊕ Fin l) ⊕ (Fin d ⊕ Fin l) → P.N |
      c ∘ Sum.inr ∈ Ycode P Y ∧ ∀ k, c (.inl k) = rvify P (c ∘ Sum.inr) k} := by
    refine ((Ycode_definable P Y).preimage_comp Sum.inr).inter ?_
    convert Set.definable_iInter_of_finite (fun k : Fin d ⊕ Fin l =>
      (Set.DefinableFun.proj LRV (i := (Sum.inl k : (Fin d ⊕ Fin l) ⊕ (Fin d ⊕ Fin l)))).ofPred_eq
        (rvify_definableMap P (S0 P) (Sum.inr : Fin d ⊕ Fin l → (Fin d ⊕ Fin l) ⊕ (Fin d ⊕ Fin l)) k)) using 1
    ext c
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  convert hT.exists_of_finite using 1
  ext w
  simp only [Ybar, Set.mem_ofPred_eq, Sum.elim_comp_inr, Sum.elim_inl]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, fun k => rfl⟩
  · rintro ⟨z, hz, hk⟩
    exact ⟨z, hz, (funext hk).symm⟩

/-! ### Moving `t` into a variable -/

theorem S0_insert : S0 P ⊆ insert (tN P).val (CC P) := subset_rfl

/-- The family over `ℂ` whose fibre at `t` is the graph of `F_t`. -/
def SG : Set (Unit ⊕ ((Fin d ⊕ Fin 0) ⊕ (Fin d ⊕ Fin l)) → P.N) :=
  Classical.choose (definable_extract_param (L := LRV) (S0_insert P) (Gcode_definable P g f Y F))

theorem SG_definable : (CC P).Definable LRV (SG P g f Y F) :=
  (Classical.choose_spec (definable_extract_param (L := LRV) (S0_insert P) (Gcode_definable P g f Y F))).1

theorem SG_iff (z : (Fin d ⊕ Fin 0) ⊕ (Fin d ⊕ Fin l) → P.N) :
    z ∈ Gcode P g f Y F ↔ Sum.elim (fun _ => (tN P).val) z ∈ SG P g f Y F :=
  (Classical.choose_spec (definable_extract_param (L := LRV) (S0_insert P) (Gcode_definable P g f Y F))).2 z

/-- The family over `ℂ` whose fibre at `t` is the RV set `Ybar`. -/
def SYb : Set (Unit ⊕ (Fin d ⊕ Fin l) → P.N) :=
  Classical.choose (definable_extract_param (L := LRV) (S0_insert P) (Ybar_definable P Y))

omit g f in
theorem SYb_definable : (CC P).Definable LRV (SYb P Y) :=
  (Classical.choose_spec (definable_extract_param (L := LRV) (S0_insert P) (Ybar_definable P Y))).1

omit g f in
theorem SYb_iff (w : Fin d ⊕ Fin l → P.N) :
    w ∈ Ybar P Y ↔ Sum.elim (fun _ => (tN P).val) w ∈ SYb P Y :=
  (Classical.choose_spec (definable_extract_param (L := LRV) (S0_insert P) (Ybar_definable P Y))).2 w

/-- The family `Y_y`: codes whose `rvify` lies in the fibre of `SYb` at `y`. -/
def Yfam : Set (Unit ⊕ (Fin d ⊕ Fin l) → P.N) :=
  {w | w ∘ Sum.inr ∈ (rawMixedSpace (M := P.N) d l).domain ∧
    Sum.elim (w ∘ Sum.inl) (rvify P (w ∘ Sum.inr)) ∈ SYb P Y}

omit g f in
theorem Yfam_definable : (CC P).Definable LRV (Yfam P Y) := by
  have hdom := ((rawMixedSpace (M := P.N) d l).domain_definable.mono (Set.empty_subset (CC P))).preimage_comp
    (Sum.inr : Fin d ⊕ Fin l → Unit ⊕ (Fin d ⊕ Fin l))
  have hmap : (CC P).DefinableMap LRV (fun w : Unit ⊕ (Fin d ⊕ Fin l) → P.N =>
      (Sum.elim (w ∘ Sum.inl) (rvify P (w ∘ Sum.inr)) : Unit ⊕ (Fin d ⊕ Fin l) → P.N)) := by
    intro k
    rcases k with u | k
    · exact Set.DefinableFun.proj LRV
    · exact rvify_definableMap P (CC P) (Sum.inr : Fin d ⊕ Fin l → Unit ⊕ (Fin d ⊕ Fin l)) k
  exact hdom.inter ((SYb_definable P Y).preimage_map hmap)

/-- The parameters `y` over which the fibre of `SG` is the graph of a bijection `𝒳_y → Y_y`. -/
def Good : Set (Unit → P.N) :=
  {y | BijGraph (fibre (famCodes P g f) y) (fibre (Yfam P Y) y) (fibre (SG P g f Y F) y)}

theorem Good_definable : (CC P).Definable LRV (Good P g f Y F) :=
  bijGraph_definable (famCodes_definable P g f) (Yfam_definable P Y) (SG_definable P g f Y F)

/-! ### The fibres at `t` -/

theorem fibre_famCodes (y : VFType (M := P.N)) :
    fibre (famCodes P g f) (fun _ => y.val) = (rawMixedSpace (M := P.N) d 0).preimage (fiberSet P g f y) := by
  ext z
  rw [mem_preimage_iff]
  constructor
  · intro hz
    have hd := famCodes_domain P g f hz
    refine ⟨_, ?_, mixedValues_decode ⟨z, hd⟩⟩
    rw [← mem_famCodes, mixedValues_decode ⟨z, hd⟩]
    exact hz
  · rintro ⟨p, hp, rfl⟩
    exact (mem_famCodes P g f y p).mpr hp

theorem rvify_mixedValues {n r : ℕ} (q : Mixed P.N n r) :
    rvify P (mixedValues q) = Sum.elim (fun i => iRv (q.1 i).val) (fun j => (q.2 j).val) := rfl

omit g f in
theorem fibre_Yfam_t (hpb : SpecialTransformations.Section5.IsRVPullback Y.carrier) :
    fibre (Yfam P Y) (fun _ => (tN P).val) = Ycode P Y := by
  ext z
  simp only [fibre, Yfam, Set.mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_comp_inr, ← SYb_iff, Ybar]
  constructor
  · rintro ⟨hd, z', hz', he⟩
    obtain ⟨q', hq', rfl⟩ := (mem_preimage_iff P _ z').mp hz'
    refine (mem_preimage_iff P _ z).mpr ⟨_, ?_, mixedValues_decode ⟨z, hd⟩⟩
    set q := (rawMixedSpace (M := P.N) d l).decode ⟨z, hd⟩
    have he' : rvify P (mixedValues q') = rvify P (mixedValues q) := by
      rw [he, mixedValues_decode ⟨z, hd⟩]
    rw [SpecialTransformations.Section5.isRVPullback_iff] at hpb
    refine hpb q' hq' q ((SpecialTransformations.Section5.sameRV_iff q' q).mpr ⟨fun i => ?_, ?_⟩)
    · exact Subtype.ext (congrFun he' (.inl i))
    · funext j
      exact Subtype.ext (congrFun he' (.inr j))
  · intro hz
    obtain ⟨q, _, rfl⟩ := (mem_preimage_iff P _ z).mp hz
    exact ⟨mixedValues_mem_domain q, _, hz, rfl⟩

theorem fibre_SG_t : fibre (SG P g f Y F) (fun _ => (tN P).val) = Gcode P g f Y F := by
  ext z
  exact (SG_iff P g f Y F z).symm

/-- `Gcode` is the graph of a bijection from the codes of `𝒳_t` onto the codes of `Y`. -/
theorem Gcode_bij : BijGraph ((rawMixedSpace (M := P.N) d 0).preimage (At P g f).carrier) (Ycode P Y)
    (Gcode P g f Y F) := by
  have hG : ∀ (x : Fin d ⊕ Fin 0 → P.N) (z : Fin d ⊕ Fin l → P.N), Sum.elim x z ∈ Gcode P g f Y F ↔
      ∃ a : At P g f, mixedValues a.val = x ∧ mixedValues (F.map.toFun a).val = z := by
    intro x z
    refine (mem_prod_preimage_iff P (graphSet P g f Y F) x z).trans ?_
    constructor
    · rintro ⟨p, w, ⟨a, ha, hw⟩, hx, hz⟩
      exact ⟨a, (congrArg mixedValues ha).trans hx, (congrArg mixedValues hw).trans hz⟩
    · rintro ⟨a, hx, hz⟩
      exact ⟨a.val, _, ⟨a, rfl, rfl⟩, hx, hz⟩
  rw [bijGraph_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x z h
    obtain ⟨a, rfl, rfl⟩ := (hG x z).mp h
    exact ⟨(mem_preimage_iff P _ _).mpr ⟨a.val, a.property, rfl⟩,
      (mem_preimage_iff P _ _).mpr ⟨_, (F.map.toFun a).property, rfl⟩⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := (mem_preimage_iff P _ x).mp hx
    exact ⟨_, (hG _ _).mpr ⟨⟨p, hp⟩, rfl, rfl⟩⟩
  · intro x z z' h1 h2
    obtain ⟨a, rfl, rfl⟩ := (hG x z).mp h1
    obtain ⟨a', ha', rfl⟩ := (hG _ z').mp h2
    have haa : a' = a := Subtype.ext (mixedValues_injective ha')
    rw [haa]
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := (mem_preimage_iff P _ z).mp hz
    obtain ⟨a, ha⟩ := F.bijective.2 ⟨w, hw⟩
    refine ⟨_, (hG _ _).mpr ⟨a, rfl, ?_⟩⟩
    have ha' : F.map.toFun a = ⟨w, hw⟩ := ha
    rw [ha']
  · intro x x' z h1 h2
    obtain ⟨a, rfl, rfl⟩ := (hG x z).mp h1
    obtain ⟨a', rfl, hz'⟩ := (hG x' _).mp h2
    have haa : a' = a := F.bijective.1 (Subtype.ext (mixedValues_injective hz'))
    rw [haa]

theorem Good_t (hpb : SpecialTransformations.Section5.IsRVPullback Y.carrier) :
    (fun _ => (tN P).val) ∈ Good P g f Y F := by
  change BijGraph _ _ _
  rw [fibre_famCodes P g f (tN P), fibre_Yfam_t P Y hpb, fibre_SG_t]
  exact Gcode_bij P g f Y F

/-! ### Transfer to `t'` with `rv(t') = rv(t)` -/

theorem rvify_rv {n r : ℕ} {z : Fin n ⊕ Fin r → P.N} (hz : z ∈ (rawMixedSpace (M := P.N) n r).domain) :
    ∀ k, iRV (rvify P z k) := by
  obtain ⟨q, rfl⟩ : ∃ q, mixedValues q = z := ⟨_, mixedValues_decode ⟨z, hz⟩⟩
  rintro (i | j)
  · exact rv_mem (inferInstance : P.N ⊨ Axioms.ACVF) (q.1 i).property
  · exact (q.2 j).property

omit g f in
theorem fibre_Yfam_t' (hpb : SpecialTransformations.Section5.IsRVPullback Y.carrier)
    {t' : VFType (M := P.N)} (h : rv P.N (tN P) = rv P.N t') :
    fibre (Yfam P Y) (fun _ => t'.val) = Ycode P Y := by
  rw [← fibre_Yfam_t P Y hpb]
  ext z
  simp only [fibre, Yfam, Set.mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_comp_inr]
  refine and_congr_right fun hd => ?_
  exact (same_type_sum (EE P) (EE_value P) P.hc (CC_mem P) (SYb P Y) (SYb_definable P Y)
    (one_lt_tN P) h (rvify P z) (rvify_rv P hd)).symm

theorem Good_t' (hpb : SpecialTransformations.Section5.IsRVPullback Y.carrier)
    {t' : VFType (M := P.N)} (h : rv P.N (tN P) = rv P.N t') :
    (fun _ => t'.val) ∈ Good P g f Y F := by
  have hU : (CC P).Definable LRV ((fun w : Unit ⊕ Empty → P.N => w ∘ Sum.inl) ⁻¹' Good P g f Y F) :=
    (Good_definable P g f Y F).preimage_comp Sum.inl
  have h0 : (Sum.elim (fun _ => (tN P).val) (Empty.elim : Empty → P.N) : Unit ⊕ Empty → P.N) ∈
      ((fun w : Unit ⊕ Empty → P.N => w ∘ Sum.inl) ⁻¹' Good P g f Y F) := by
    show _ ∘ Sum.inl ∈ Good P g f Y F
    rw [Sum.elim_comp_inl]
    exact Good_t P g f Y F hpb
  have h1 := (same_type_sum (EE P) (EE_value P) P.hc (CC_mem P) _ hU (one_lt_tN P) h
    (Empty.elim : Empty → P.N) (fun j => j.elim)).mp h0
  change _ ∘ Sum.inl ∈ Good P g f Y F at h1
  rwa [Sum.elim_comp_inl] at h1

/-- **The bijections `F_{t'}`.** For `rv(t') = rv(t)`, the fibre of `SG` at `t'` is the graph of a
bijection from the codes of `𝒳_{t'}` onto the codes of `Y`. -/
theorem bij_t' (hpb : SpecialTransformations.Section5.IsRVPullback Y.carrier)
    {t' : VFType (M := P.N)} (h : rv P.N (tN P) = rv P.N t') :
    BijGraph ((rawMixedSpace (M := P.N) d 0).preimage (fiberSet P g f t')) (Ycode P Y)
      (fibre (SG P g f Y F) (fun _ => t'.val)) := by
  have hg := Good_t' P g f Y F hpb h
  change BijGraph _ _ _ at hg
  rwa [fibre_famCodes P g f t', fibre_Yfam_t' P Y hpb h] at hg

end Data

/-! ### The point `rv(t)^♯` -/

/-- `rv(t)` is in the definable closure of the base of Section 8. -/
theorem rvt_closure : DefinableClosureAtBase P.G.base .rv (iRv (tN P).val) := by
  have hraw : (P.G.real : Set P.N).Definable LRV {z : Fin 1 → P.N | z 0 ∈ ({iRv (tN P).val} : Set P.N)} := by
    have hc : (P.G.real : Set P.N).DefinableFun LRV (fun _ : Fin 1 → P.N => iRv (tN P).val) :=
      (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := P.N) (L := LRV) Fn.rvMap)).comp
        (show (P.G.real : Set P.N).DefinableMap LRV (fun _ : Fin 1 → P.N => ![(tN P).val]) from by
          intro k
          fin_cases k
          exact LRV.definableFun_const _ (tN_mem P))
    convert (Set.DefinableFun.proj LRV (i := (0 : Fin 1))).ofPred_eq hc using 1
    ext z
    exact Set.mem_singleton_iff
  have h := (DiamondIntegral.Section5.emptyGamma_sorted_definable_iff P.hc (P.G.real : Set P.N)
    (fun _ : Fin 1 => SortTag.rv) _).mpr ⟨hraw, fun x hx i => ?_⟩
  · exact h.mono subset_rfl (Set.empty_subset _)
  · have hx0 : x i = iRv (tN P).val := by
      rw [Subsingleton.elim i 0]
      exact hx
    rw [hx0]
    exact rv_mem (inferInstance : P.N ⊨ Axioms.ACVF) (tN P).property

theorem rvt_ne_zero : iRv (tN P).val ≠ iRVZero := by
  intro hz
  have h0 : tN P = 0 := (CanonicalRV.encodedRv_zero_iff (tN P)).mp hz
  have hv := value_tN P
  rw [h0, map_zero, ← Values.infinity_eq_zero] at hv
  exact (piV P).property hv.symm

/-- The code `1 ∈ RV`, as a point of `RV¹`. -/
def c1 : Fin 1 → CanonicalRV.RVSort P.N := fun i =>
  ⟨RESPointTuples.tuple 1 i, ((RESPointTuples.chart P.G.base 1).coordinate_proper _ rfl i).1⟩

/-- `rv(t)`, as a point of `RV¹`. -/
def cv : Fin 1 → CanonicalRV.RVSort P.N := fun _ => rv P.N (tN P)

/-- The domain `{1} ⊆ RV¹`. -/
def UtDom : GammaGroundDefSet P.hc P.G.base (rawRVSpace (M := P.N) 1) :=
  ⟨{c1 P}, gammaGroundDefinable_iff_rvBase.mpr (by
    rw [Set.image_singleton]
    exact RESPointTuples.tuple_definable _ 1)⟩

/-- The constant volume `rv(t)`. -/
def UtVol : GammaGroundMap (UtDom P) (GammaGroundDefSet.univ P.hc P.G.base (rawRVSpace (M := P.N) 1)) :=
  GammaGroundMap.const (UtDom P) (cv P) (gammaGroundDefinable_iff_rvBase.mpr (by
    rw [Set.image_singleton]
    exact tuple_singleton_definable_base _ _ _ (fun _ => rvt_closure P)))

/-- The RV object `({1}, rv(t))`, whose lift is `rv(t)^♯ × {1}`. -/
def Ut : GammaGroundRVObject P.hc P.G.base 1 where
  arity := 1
  domain := UtDom P
  volume := UtVol P
  finite _ := by
    have : Finite (UtDom P).carrier := (Set.finite_singleton (c1 P)).to_subtype
    exact Set.toFinite _
  nonzero _ _ := rvt_ne_zero P

/-- `rv(t)^♯ × {1}` over the base of Section 8. -/
abbrev RObj : GammaGroundFiniteVFObject P.hc P.G.base := gammaGroundObjectLiftFinite (Ut P)

theorem mem_RObj (q : Mixed P.N 1 1) :
    q ∈ (RObj P).domain.carrier ↔ q.2 = c1 P ∧ rv P.N (q.1 0) = rv P.N (tN P) := by
  change (∃ u : UtDom P, u.val = q.2 ∧ ((UtVol P).toFun u).val = Section2.tupleRV P.N q.1) ↔ _
  constructor
  · rintro ⟨u, hu, hv⟩
    have hu1 : u.val = c1 P := u.property
    refine ⟨hu.symm.trans hu1, ?_⟩
    have := congrFun hv 0
    exact this.symm
  · rintro ⟨h2, h1⟩
    refine ⟨⟨c1 P, rfl⟩, h2.symm, ?_⟩
    funext i
    rw [Subsingleton.elim i 0]
    exact h1.symm

/-- The chart of `({1}, rv(t))` and the point chart `{1}` have the same underlying set. -/
def pointIso : RVForgetScissors.UnderlyingIso (Section3RVChartBridge.chart (Ut P))
    (RESPointTuples.chart P.G.base 1) := by
  have hdom : (Section3RVChartBridge.chart (Ut P)).domain = {RESPointTuples.tuple 1} := by
    change rvValues '' {c1 P} = _
    rw [Set.image_singleton]
    rfl
  refine RVForgetScissors.ofMap _ _ id ?_ ?_
  · rw [hdom]
    exact RVSharpCharts.identity_graph_definable _ _ (RESPointTuples.tuple_definable _ 1)
  · rw [hdom]
    exact Set.bijOn_id _

/-- **`∫[rv(t)^♯] = [1]`.** -/
theorem integral_RObj :
    nativeVFChartIntegral (completed18GroundLiftInput P.G P.hc)
        (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (RObj P))) =
      RVOrdinaryPNormalization.quotient P.G.base
        (RVOrdinaryRing.objectClass (RESPointTuples.chart P.G.base 1)) := by
  rw [nativeVFChartIntegral_lift_class, RVOrdinaryRing.objectClass_iso (pointIso P)]

/-! ### `𝒳_t`, `Y` and `𝒳_f` over the base of Section 8 -/

/-- `𝒳_t` over the base of Section 8. -/
def XtObj : GammaGroundFiniteVFObject P.hc P.G.base :=
  ⟨d, 0, (At P g f).monoBase (S0_sub_real P) (Set.empty_subset _), fun _ => Set.toFinite _⟩

/-- `𝒳_f = {x ∈ X(𝔪) | rv(f(x)) = rv(t)}` over the base of Section 8 (`sourceSet`). -/
abbrev XfObj : GammaGroundFiniteVFObject P.hc P.G.base :=
  ⟨d, 0, GammaGroundDefSet.ofReal (sourceDefSet P g f), fun _ => Set.toFinite _⟩

section Data2

variable {l : ℕ} (Y : GammaGroundDefSet P.hc (B0 P) (rawMixedSpace (M := P.N) d l))
  (F : GammaGroundBijection (At P g f) Y)

include F in
theorem Y_finite : ∀ b : Fin d → Section2.VF P.N, {u | (b, u) ∈ Y.carrier}.Finite :=
  (gammaGroundFiniteRVFibres_iff F P.G.uncountable.le P.G.saturated P.G.model00 (S0_small P)).mp
    (fun _ => Set.toFinite _)

/-- `Y` over the base of Section 8. -/
def YObj : GammaGroundFiniteVFObject P.hc P.G.base :=
  ⟨d, l, Y.monoBase (S0_sub_real P) (Set.empty_subset _), Y_finite P g f Y F⟩

theorem class_Xt_Y : gammaGroundVFSemiringClass (XtObj P g f) = gammaGroundVFSemiringClass (YObj P g f Y F) :=
  nativePositiveVFClass_bijection ⟨F.map.monoBase (S0_sub_real P) (Set.empty_subset _), F.bijective⟩

end Data2

/-! ### The bijection `𝒳_f → rv(t)^♯ × Y`, `x ↦ (f(x), F_{f(x)}(x))` -/

/-- `f(x)`. -/
abbrev sv (p : Mixed P.N d 0) : VFType (M := P.N) := MvPolynomial.eval p.1 (fN P f)

theorem rv_sv {p : Mixed P.N d 0} (hp : p ∈ sourceSet P g f) : rv P.N (tN P) = rv P.N (sv P f p) :=
  hp.2.symm

theorem mem_fiber_sv {p : Mixed P.N d 0} (hp : p ∈ sourceSet P g f) : p ∈ fiberSet P g f (sv P f p) :=
  ⟨hp.1, rfl⟩

/-- The index map placing `(y, x, z)` among the codes of `(x, (y, 1, z))`. -/
def hidx (d l : ℕ) : Unit ⊕ ((Fin d ⊕ Fin 0) ⊕ (Fin d ⊕ Fin l)) →
    (Fin d ⊕ Fin 0) ⊕ (Fin (1 + d) ⊕ Fin (1 + l)) :=
  Sum.elim (fun _ => .inr (.inl (Fin.castAdd d 0)))
    (Sum.elim Sum.inl (Sum.elim (fun i => .inr (.inl (Fin.natAdd 1 i))) (fun j => .inr (.inr (Fin.natAdd 1 j)))))

theorem comp_hidx {l : ℕ} (p : Mixed P.N d 0) (w : Mixed P.N (1 + d) (1 + l)) :
    (Sum.elim (mixedValues p) (mixedValues w) : (Fin d ⊕ Fin 0) ⊕ (Fin (1 + d) ⊕ Fin (1 + l)) → P.N) ∘ hidx d l =
      Sum.elim (fun _ => (w.1 (Fin.castAdd d 0)).val)
        (Sum.elim (mixedValues p) (mixedValues (w.1 ∘ Fin.natAdd 1, w.2 ∘ Fin.natAdd 1))) := by
  funext k
  rcases k with _ | (x | (i | j)) <;> rfl

section Phi

variable {l : ℕ} (Y : GammaGroundDefSet P.hc (B0 P) (rawMixedSpace (M := P.N) d l))
  (F : GammaGroundBijection (At P g f) Y)
  (hpb : SpecialTransformations.Section5.IsRVPullback Y.carrier)

include hpb in
theorem img_exists {p : Mixed P.N d 0} (hp : p ∈ sourceSet P g f) :
    ∃ q : Mixed P.N d l, q ∈ Y.carrier ∧
      Sum.elim (mixedValues p) (mixedValues q) ∈ fibre (SG P g f Y F) (fun _ => (sv P f p).val) := by
  have hb := bijGraph_iff.mp (bij_t' P g f Y F hpb (rv_sv P g f hp))
  obtain ⟨z, hz⟩ := hb.2.1 (mixedValues p) ((mem_preimage_iff P _ _).mpr ⟨p, mem_fiber_sv P g f hp, rfl⟩)
  obtain ⟨q, hq, rfl⟩ := (mem_preimage_iff P _ z).mp (hb.1 _ _ hz).2
  exact ⟨q, hq, hz⟩

/-- `F_{f(x)}(x)`. -/
def img {p : Mixed P.N d 0} (hp : p ∈ sourceSet P g f) : Mixed P.N d l :=
  Classical.choose (img_exists P g f Y F hpb hp)

theorem img_spec {p : Mixed P.N d 0} (hp : p ∈ sourceSet P g f) :
    img P g f Y F hpb hp ∈ Y.carrier ∧ Sum.elim (mixedValues p) (mixedValues (img P g f Y F hpb hp)) ∈
      fibre (SG P g f Y F) (fun _ => (sv P f p).val) :=
  Classical.choose_spec (img_exists P g f Y F hpb hp)

theorem img_unique {p : Mixed P.N d 0} (hp : p ∈ sourceSet P g f) {q : Mixed P.N d l}
    (hq : Sum.elim (mixedValues p) (mixedValues q) ∈ fibre (SG P g f Y F) (fun _ => (sv P f p).val)) :
    q = img P g f Y F hpb hp :=
  mixedValues_injective ((bijGraph_iff.mp (bij_t' P g f Y F hpb (rv_sv P g f hp))).2.2.1 _ _ _ hq
    (img_spec P g f Y F hpb hp).2)

/-- `x ↦ (f(x), 1, F_{f(x)}(x))`. -/
def phiPt {p : Mixed P.N d 0} (hp : p ∈ sourceSet P g f) : Mixed P.N (1 + d) (1 + l) :=
  (Fin.append (fun _ : Fin 1 => sv P f p) (img P g f Y F hpb hp).1, Fin.append (c1 P) (img P g f Y F hpb hp).2)

theorem phiPt_mem {p : Mixed P.N d 0} (hp : p ∈ sourceSet P g f) :
    phiPt P g f Y F hpb hp ∈ ((RObj P).product (YObj P g f Y F)).domain.carrier := by
  change _ ∈ (gammaGroundMixedProductDomain _ _).carrier
  rw [mem_gammaGroundMixedProductDomain]
  refine ⟨(mem_RObj P _).mpr ⟨?_, ?_⟩, ?_⟩
  · funext i
    exact Fin.append_left _ _ i
  · exact (rv_sv P g f hp).symm
  · have h := (img_spec P g f Y F hpb hp).1
    have e : ((phiPt P g f Y F hpb hp).1 ∘ Fin.natAdd 1, (phiPt P g f Y F hpb hp).2 ∘ Fin.natAdd 1) =
        img P g f Y F hpb hp := by
      refine Prod.ext ?_ ?_ <;> funext i <;> simp [phiPt, Fin.append_right]
    have h' : ((phiPt P g f Y F hpb hp).1 ∘ Fin.natAdd 1, (phiPt P g f Y F hpb hp).2 ∘ Fin.natAdd 1) ∈ Y.carrier := by
      rw [e]
      exact h
    exact h'

/-- The map `𝒳_f → rv(t)^♯ × {1} × Y`. -/
def phiFun (a : (XfObj P g f).domain) : ((RObj P).product (YObj P g f Y F)).domain :=
  ⟨phiPt P g f Y F hpb a.property, phiPt_mem P g f Y F hpb a.property⟩

theorem graph_iff (p : Mixed P.N d 0) (w : Mixed P.N (1 + d) (1 + l)) :
    (∃ a : (XfObj P g f).domain, a.val = p ∧ (phiFun P g f Y F hpb a).val = w) ↔
      p ∈ sourceSet P g f ∧ w.1 (Fin.castAdd d 0) = sv P f p ∧ w.2 (Fin.castAdd l 0) = c1 P 0 ∧
        Sum.elim (mixedValues p) (mixedValues (w.1 ∘ Fin.natAdd 1, w.2 ∘ Fin.natAdd 1)) ∈
          fibre (SG P g f Y F) (fun _ => (w.1 (Fin.castAdd d 0)).val) := by
  constructor
  · rintro ⟨a, rfl, rfl⟩
    have e : ((phiPt P g f Y F hpb a.property).1 ∘ Fin.natAdd 1, (phiPt P g f Y F hpb a.property).2 ∘ Fin.natAdd 1) =
        img P g f Y F hpb a.property := by
      refine Prod.ext ?_ ?_ <;> funext i <;> simp [phiPt, Fin.append_right]
    refine ⟨a.property, ?_, ?_, ?_⟩
    · simp only [phiFun, phiPt]
      exact Fin.append_left _ _ _
    · simp only [phiFun, phiPt]
      exact Fin.append_left _ _ _
    change Sum.elim (mixedValues a.val) (mixedValues ((phiPt P g f Y F hpb a.property).1 ∘ Fin.natAdd 1,
      (phiPt P g f Y F hpb a.property).2 ∘ Fin.natAdd 1)) ∈
        fibre (SG P g f Y F) (fun _ => ((phiPt P g f Y F hpb a.property).1 (Fin.castAdd d 0)).val)
    rw [e]
    exact (img_spec P g f Y F hpb a.property).2
  · rintro ⟨hp, h1, h2, h3⟩
    refine ⟨⟨p, hp⟩, rfl, ?_⟩
    rw [h1] at h3
    have hq := img_unique P g f Y F hpb hp h3
    change (Fin.append (fun _ : Fin 1 => sv P f p) (img P g f Y F hpb hp).1,
      Fin.append (c1 P) (img P g f Y F hpb hp).2) = w
    rw [← hq]
    have e1 : (fun _ : Fin 1 => sv P f p) = w.1 ∘ Fin.castAdd d := by
      funext j
      rw [Subsingleton.elim j 0]
      exact h1.symm
    have e2 : c1 P = w.2 ∘ Fin.castAdd l := by
      funext j
      rw [Subsingleton.elim j 0]
      exact h2.symm
    rw [e1, e2]
    exact Prod.ext Fin.append_castAdd_natAdd Fin.append_castAdd_natAdd

/-- The codes of the graph of `phiFun`. -/
def Tcodes : Set ((Fin d ⊕ Fin 0) ⊕ (Fin (1 + d) ⊕ Fin (1 + l)) → P.N) :=
  {c | c ∘ Sum.inl ∈ (rawMixedSpace (M := P.N) d 0).domain ∧
    c ∘ Sum.inr ∈ (rawMixedSpace (M := P.N) (1 + d) (1 + l)).domain ∧
    c ∘ Sum.inl ∈ sourceCodes P g f ∧
    c (.inr (.inl (Fin.castAdd d 0))) = SpecialTransformations.Section5.mvPolynomialCode (fN P f) (c ∘ Sum.inl) ∧
    c (.inr (.inr (Fin.castAdd l 0))) = RESPointTuples.tuple 1 0 ∧
    c ∘ hidx d l ∈ SG P g f Y F}

theorem Tcodes_definable : (P.G.real : Set P.N).Definable LRV (Tcodes P g f Y F) := by
  have h1 := ((rawMixedSpace (M := P.N) d 0).domain_definable.mono (Set.empty_subset (P.G.real : Set P.N))).preimage_comp
    (Sum.inl : Fin d ⊕ Fin 0 → (Fin d ⊕ Fin 0) ⊕ (Fin (1 + d) ⊕ Fin (1 + l)))
  have h2 := ((rawMixedSpace (M := P.N) (1 + d) (1 + l)).domain_definable.mono (Set.empty_subset (P.G.real : Set P.N))).preimage_comp
    (Sum.inr : Fin (1 + d) ⊕ Fin (1 + l) → (Fin d ⊕ Fin 0) ⊕ (Fin (1 + d) ⊕ Fin (1 + l)))
  have h3 := (sourceCodes_definable P g f).preimage_comp
    (Sum.inl : Fin d ⊕ Fin 0 → (Fin d ⊕ Fin 0) ⊕ (Fin (1 + d) ⊕ Fin (1 + l)))
  have hp := SpecialTransformations.Section5.mvPolynomialCode_definable (m := 0) (S := (P.G.real : Set P.N))
    (fN P f) (fN_coeff_mem P f)
  change @Set.DefinableFun P.N LRV (CanonicalStructure.normalize (M := P.N)) (Fin d ⊕ Fin 0)
    (P.G.real : Set P.N) (SpecialTransformations.Section5.mvPolynomialCode (m := 0) (fN P f)) at hp
  rw [SpecialTransformations.Section4.canonical_normalize_eq P.hc] at hp
  have h4 := (Set.DefinableFun.proj LRV (A := (P.G.real : Set P.N))
    (i := (Sum.inr (Sum.inl (Fin.castAdd d 0)) : (Fin d ⊕ Fin 0) ⊕ (Fin (1 + d) ⊕ Fin (1 + l))))).ofPred_eq
    (hp.comp (g := fun v : (Fin d ⊕ Fin 0) ⊕ (Fin (1 + d) ⊕ Fin (1 + l)) → P.N => v ∘ Sum.inl)
      (fun _ => Set.DefinableFun.proj LRV))
  have hone := ((DiamondIntegral.Section5.emptyGamma_sorted_definable_iff P.hc (P.G.real : Set P.N)
    (fun _ : Fin 1 => SortTag.rv) _).mp (RVRadiusGenerators.oneCode_definable (EmptyGammaGround.base _))).1
  have h5 := hone.preimage_comp (fun _ : Fin 1 =>
    (Sum.inr (Sum.inr (Fin.castAdd l 0)) : (Fin d ⊕ Fin 0) ⊕ (Fin (1 + d) ⊕ Fin (1 + l))))
  have h6 := ((SG_definable P g f Y F).mono (CC_sub_real P)).preimage_comp (hidx d l)
  convert h1.inter (h2.inter (h3.inter (h4.inter (h5.inter h6)))) using 1
  ext c
  simp only [Tcodes, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Function.comp_apply]
  rfl

theorem phi_graph_definable :
    ((rawMixedSpace (M := P.N) d 0).prod (rawMixedSpace (M := P.N) (1 + d) (1 + l))).Definable
      (P.G.real : Set P.N) {z | ∃ a : (XfObj P g f).domain, a.val = z.1 ∧ (phiFun P g f Y F hpb a).val = z.2} := by
  have key : ∀ (x : Fin d ⊕ Fin 0 → P.N) (z : Fin (1 + d) ⊕ Fin (1 + l) → P.N),
      (Sum.elim x z : (Fin d ⊕ Fin 0) ⊕ (Fin (1 + d) ⊕ Fin (1 + l)) → P.N) ∈
          Space.preimage ((rawMixedSpace (M := P.N) d 0).prod (rawMixedSpace (M := P.N) (1 + d) (1 + l)))
            {z | ∃ a : (XfObj P g f).domain, a.val = z.1 ∧ (phiFun P g f Y F hpb a).val = z.2} ↔
        Sum.elim x z ∈ Tcodes P g f Y F := by
    intro x z
    refine (mem_prod_preimage_iff P _ x z).trans ?_
    constructor
    · rintro ⟨p, w, hgraph, rfl, rfl⟩
      obtain ⟨hp, h1, h2, h3⟩ := (graph_iff P g f Y F hpb p w).mp hgraph
      refine ⟨mixedValues_mem_domain p, mixedValues_mem_domain w, (mem_sourceCodes_iff P g f p).mpr hp, ?_, ?_, ?_⟩
      · have hcode := SpecialTransformations.Section5.mvPolynomialCode_eq (fN P f) (mixedValues p) p.1
          (fun i => rfl)
        exact (congrArg Subtype.val h1).trans hcode.symm
      · exact congrArg Subtype.val h2
      · rw [comp_hidx]
        exact h3
    · rintro ⟨hx, hz, hm, hc, ho, hs⟩
      obtain ⟨p, rfl⟩ : ∃ p, mixedValues p = x := ⟨_, mixedValues_decode ⟨x, hx⟩⟩
      obtain ⟨w, rfl⟩ : ∃ w, mixedValues w = z := ⟨_, mixedValues_decode ⟨z, hz⟩⟩
      refine ⟨p, w, (graph_iff P g f Y F hpb p w).mpr ⟨(mem_sourceCodes_iff P g f p).mp hm, ?_, ?_, ?_⟩, rfl, rfl⟩
      · have hcode := SpecialTransformations.Section5.mvPolynomialCode_eq (fN P f) (mixedValues p) p.1
          (fun i => rfl)
        exact Subtype.ext (hc.trans hcode)
      · exact Subtype.ext ho
      · change _ ∘ hidx d l ∈ SG P g f Y F at hs
        rw [comp_hidx] at hs
        exact hs
  have hset : (Tcodes P g f Y F : Set ((Fin d ⊕ Fin 0) ⊕ (Fin (1 + d) ⊕ Fin (1 + l)) → P.N)) =
      Space.preimage ((rawMixedSpace (M := P.N) d 0).prod (rawMixedSpace (M := P.N) (1 + d) (1 + l)))
        {z | ∃ a : (XfObj P g f).domain, a.val = z.1 ∧ (phiFun P g f Y F hpb a).val = z.2} := by
    ext c
    simpa only [Sum.elim_comp_inl_inr] using (key (c ∘ Sum.inl) (c ∘ Sum.inr)).symm
  change (P.G.real : Set P.N).Definable LRV (Space.preimage _ _)
  exact hset ▸ Tcodes_definable P g f Y F

/-- The bijection `𝒳_f → rv(t)^♯ × {1} × Y`, definable over the base of Section 8. -/
def PhiMap : GammaGroundMap (XfObj P g f).domain ((RObj P).product (YObj P g f Y F)).domain where
  toFun := phiFun P g f Y F hpb
  graph_definable := GammaGroundDefinable.of_real (phi_graph_definable P g f Y F hpb)

theorem PhiMap_bijective : Function.Bijective (PhiMap P g f Y F hpb) := by
  constructor
  · intro a a' h
    have h' : phiPt P g f Y F hpb a.property = phiPt P g f Y F hpb a'.property := congrArg Subtype.val h
    have hs : sv P f a.val = sv P f a'.val := by
      have := congrFun (congrArg Prod.fst h') (Fin.castAdd d 0)
      simpa [phiPt, Fin.append_left] using this
    have hq : img P g f Y F hpb a.property = img P g f Y F hpb a'.property := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · have := congrFun (congrArg Prod.fst h') (Fin.natAdd 1 i)
        simpa [phiPt, Fin.append_right] using this
      · have := congrFun (congrArg Prod.snd h') (Fin.natAdd 1 i)
        simpa [phiPt, Fin.append_right] using this
    have e1 := (img_spec P g f Y F hpb a.property).2
    have e2 := (img_spec P g f Y F hpb a'.property).2
    rw [← hs, ← hq] at e2
    have hb := bijGraph_iff.mp (bij_t' P g f Y F hpb (rv_sv P g f a.property))
    exact Subtype.ext (mixedValues_injective (hb.2.2.2.2 _ _ _ e1 e2))
  · rintro ⟨w, hw⟩
    change Mixed P.N (1 + d) (1 + l) at w
    have hw' := hw
    change w ∈ (gammaGroundMixedProductDomain _ _).carrier at hw'
    rw [mem_gammaGroundMixedProductDomain] at hw'
    obtain ⟨hR, hY⟩ := hw'
    obtain ⟨hc1, hrv⟩ := (mem_RObj P _).mp hR
    have hrv' : rv P.N (tN P) = rv P.N (w.1 (Fin.castAdd d 0)) := hrv.symm
    have hc1' : w.2 (Fin.castAdd l 0) = c1 P 0 := congrFun hc1 0
    have hY' : (w.1 ∘ Fin.natAdd 1, w.2 ∘ Fin.natAdd 1) ∈ Y.carrier := hY
    have hb := bijGraph_iff.mp (bij_t' P g f Y F hpb hrv')
    obtain ⟨x, hx⟩ := hb.2.2.2.1 (mixedValues (w.1 ∘ Fin.natAdd 1, w.2 ∘ Fin.natAdd 1))
      ((mem_preimage_iff P _ _).mpr ⟨_, hY', rfl⟩)
    obtain ⟨p, hp, rfl⟩ := (mem_preimage_iff P _ x).mp (hb.1 _ _ hx).1
    have hpm : p ∈ sourceSet P g f := ⟨hp.1, by rw [hp.2]; exact hrv'.symm⟩
    obtain ⟨a, rfl, ha⟩ := (graph_iff P g f Y F hpb p w).mpr ⟨hpm, hp.2.symm, hc1', hx⟩
    exact ⟨a, Subtype.ext ha⟩

include F hpb in
/-- `[𝒳_f] = [rv(t)^♯] [𝒳_t]` for a given preparation of `𝒳_t`. -/
theorem class_Xf_eq : gammaGroundVFSemiringClass (XfObj P g f) =
    gammaGroundVFSemiringClass (RObj P) * gammaGroundVFSemiringClass (XtObj P g f) := by
  rw [nativePositiveVFClass_bijection ⟨PhiMap P g f Y F hpb, PhiMap_bijective P g f Y F hpb⟩,
    gammaGroundVFSemiringClass_product, class_Xt_Y P g f Y F]

end Phi

/-! ### Remark 8.15 -/

/-- **`[𝒳_f] = [rv(t)^♯] [𝒳_t]`** in the Grothendieck semiring of VF over the base of Section 8. -/
theorem remark_8_15_class : gammaGroundVFSemiringClass (XfObj P g f) =
    gammaGroundVFSemiringClass (RObj P) * gammaGroundVFSemiringClass (XtObj P g f) := by
  obtain ⟨l, Y, ⟨F⟩, hpb⟩ := native_arbitrary_vf_pullback_preparation P.G.uncountable P.G.saturated
    P.G.model00 (S0_small P) (At P g f)
  exact class_Xf_eq P g f Y F hpb

/-- **Remark 8.15, first identity: `∫[𝒳_f] = [1] ∫[𝒳_t]`**, with `[1]` the class of the point
`1 ∈ RV¹` in `K RV[*]/(P − 1)`. -/
theorem remark_8_15_integral :
    nativeVFChartIntegral (completed18GroundLiftInput P.G P.hc)
        (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (XfObj P g f))) =
      RVOrdinaryPNormalization.quotient P.G.base (RVOrdinaryRing.objectClass (RESPointTuples.chart P.G.base 1)) *
        nativeVFChartIntegral (completed18GroundLiftInput P.G P.hc)
          (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (XtObj P g f))) := by
  rw [remark_8_15_class, ← Algebra.GrothendieckAddGroup.of_mul_of, map_mul, integral_RObj]

/-- **Remark 8.15 (`rem-comp-milnor-fib-bis`): `Vol([𝒳_f]) = Vol([𝒳_t])`.** -/
theorem remark_8_15 :
    puiseuxBoundedVFVolume P (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (XfObj P g f))) =
      puiseuxBoundedVFVolume P (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (XtObj P g f))) := by
  rw [VolComparison.vol_eq, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
    remark_8_15_integral, map_mul, VolComparison.Eb_quotient, nativeRVEvaluation_point, one_mul]

/-! ### `X = 𝔸^d` and smooth affine `X` -/

/-- No equations: `X = 𝔸^d`. -/
abbrev g0 : Fin 0 → MvPolynomial (Fin d) ℂ := fun j => j.elim0

omit g in
theorem milnor_source_eq :
    (Remark728.forgetVF P.hc P.G (milnorObject P f)).domain.carrier = (XfObj P (g0 (d := d)) f).domain.carrier := by
  ext p
  change p ∈ milnorSet P f ↔ p ∈ sourceSet P (g0 (d := d)) f
  simp [milnorSet, sourceSet, tube]

omit g in
theorem XtObj_affine (p : Mixed P.N d 0) :
    p ∈ (XtObj P (g0 (d := d)) f).domain.carrier ↔
      (∀ i, 1 < Values.vfValueHom (p.1 i)) ∧ MvPolynomial.eval p.1 (fN P f) = tN P := by
  change p ∈ fiberSet P (g0 (d := d)) f (tN P) ↔ _
  simp [fiberSet, tube]

omit g in
/-- **Remark 8.15 for `X = 𝔸^d`**: `Vol([𝒳_f]) = Vol([𝒳_t])`, `𝒳_t = {x ∈ 𝔪^d | f(x) = t}`
(`XtObj_affine`). -/
theorem remark_8_15_affine :
    puiseuxBoundedVFVolume P (Algebra.GrothendieckAddGroup.of
        (gammaGroundVFSemiringClass (Remark728.forgetVF P.hc P.G (milnorObject P f)))) =
      puiseuxBoundedVFVolume P (Algebra.GrothendieckAddGroup.of
        (gammaGroundVFSemiringClass (XtObj P (g0 (d := d)) f))) := by
  rw [nativePositiveVFClass_bijection (D := Remark728.forgetVF P.hc P.G (milnorObject P f))
    (E := XfObj P (g0 (d := d)) f) (GammaGroundBijection.ofCarrierEq (milnor_source_eq P f))]
  exact remark_8_15 P _ f

section Smooth

variable {e : ℕ} {q : Fin (e + 1) → MvPolynomial (Fin d) ℂ}

/-- The étale chart `q` as a definable bijection from `𝒳_f ⊆ X(𝔪)` onto `𝒳_f` in chart coordinates. -/
def chartBij (hq : EtaleChart P g q) : GammaGroundBijection (XfObj P g f).domain
    (Remark728.forgetVF P.hc P.G (milnorObjectX P f hq)).domain :=
  ⟨⟨(Truncation.chartCo P g f q).toFun, GammaGroundDefinable.of_real
    ((relationDefinable_iff_product _).mp (Truncation.chartCo P g f q).graph_definable)⟩,
    Truncation.chartCo_bijective (f := f) hq⟩

/-- **Remark 8.15 for smooth affine `X`** (étale chart hypothesis): `Vol([𝒳_f]) = Vol([𝒳_t])`,
with `𝒳_t = {x ∈ X(𝔪) | f(x) = t}`. -/
theorem remark_8_15_smooth (hq : EtaleChart P g q) :
    puiseuxBoundedVFVolume P (Algebra.GrothendieckAddGroup.of
        (gammaGroundVFSemiringClass (Remark728.forgetVF P.hc P.G (milnorObjectX P f hq)))) =
      puiseuxBoundedVFVolume P (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (XtObj P g f))) := by
  rw [← nativePositiveVFClass_bijection (chartBij P g f hq)]
  exact remark_8_15 P g f

end Smooth

section Milnor

open DiamondIntegral.Section8.Hm RationalSeries

variable (Gv : Type) [LinearOrderedCommGroupWithZero Gv] [Valued (VF P.N) Gv]
variable (hv : ∀ x y : VF P.N, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hntB : ∃ x : P.G.fieldBase.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

omit g in
/-- **`𝒮_f = Vol([𝒳_f]) = Vol([𝒳_t])`** for `X = 𝔸^d` (Remarks 8.14 and 8.15). -/
theorem remark_8_15_milnor :
    milnorClass P Gv hv hntB f =
      puiseuxBoundedVFVolume P (Algebra.GrothendieckAddGroup.of
        (gammaGroundVFSemiringClass (XtObj P (g0 (d := d)) f))) :=
  (VolComparison.remark_8_14_milnor P Gv hv hntB f).trans (remark_8_15_affine P f)

/-- **`𝒮_f = −lim Z_f = Vol([𝒳_t])`** for smooth affine `X` (Theorem 8.11, Remarks 8.14 and 8.15). -/
theorem remark_8_15_milnor_smooth {e : ℕ} {q : Fin (e + 1) → MvPolynomial (Fin d) ℂ} (hq : EtaleChart P g q) :
    HasLimit Lunit (zetaQ P (milnorIntegralX P f Gv hv hntB hq))
      (-(algebraMap EquivariantVariety.ModifiedRing Rloc (puiseuxBoundedVFVolume P
        (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (XtObj P g f)))))) := by
  rw [← remark_8_15_smooth P g f hq]
  exact milnor_fiber_vol_smooth P f Gv hv hntB hq

end Milnor

end DiamondIntegral.Section8.Remark815
