import «section 5».VarietyCorollaryDischarged
import «section 5».PuiseuxAmbientVFFubiniVanishing
import «section 5».VFFieldContext
import «section 5».VFFieldGammaNames
import «section 5».PuiseuxLaurentNontrivial
import CanonicalTheory
import Mathlib.ModelTheory.Ultraproducts
import Mathlib.ModelTheory.DirectLimit
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Order.Zorn
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # The saturated ambient model of Notation 5.15 and Corollary 5.21

`ambientBoundedVFVolume` (Notation 5.15) and `corollary_global_vanishing_discharged`
(Corollary 5.21) take an elementary extension `e : Carrier ↪ₑ N` of the concrete
Puiseux model, a `GammaGroundContext N` whose real base is the image of the Laurent
coefficients, canonicity of `N` and definability of the Gamma names. This file
constructs such data. Those statements are therefore not vacuous.

* `MonsterModels.exists_saturated_homogeneous_extension`: for a language in `Type`
  and a regular cardinal `κ`, every nonempty structure has a `κ`-saturated,
  strongly `κ`-homogeneous elementary extension. This is the standard ZFC existence
  theorem for monster models (see Marker, *Model Theory: An Introduction*, §4.3),
  proved here from Mathlib with no set-theoretic hypothesis. One step is an
  ultrapower indexed by finite sets of conditions. By Łoś it realizes every
  finitely satisfiable type over `M` and extends every partial elementary map of
  `M` to an elementary map into the ultrapower. Two steps are iterated along
  `κ.ord.ToType` by Mathlib's transfinite iteration, in the category of structures
  and elementary embeddings. Directed colimits in that category are direct limits.
  Regularity gives saturation of the union. Strong homogeneity is a back-and-forth
  argument organized by Zorn's lemma.
* `PuiseuxOriginal.exists_puiseux_ambient`: the binders of Corollary 5.21 are
  satisfiable. The real base is `vfFieldSubstructure` of the actual image of
  `C((t))`, equal to `Set.range (e ∘ laurentCoefficientEnumeration)`.
* `puiseuxAmbient`, `puiseuxComplexVarietyVolume`,
  `puiseux_corollary_global_vanishing` and `puiseuxBoundedVFVolume` instantiate
  the statements.

Independence of `Vol` from the chosen ambient and bijectivity of
`elementaryRESReducedRestriction` are not proved here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace DiamondIntegral.Section5.MonsterModels
open Classical FirstOrder FirstOrder.Language Structure Filter Cardinal

variable {L : FirstOrder.Language.{0, 0}}

/-! ## Generic saturation and strong homogeneity, in the project's exact shape -/

def FinSat {M : Type} [L.Structure M] {α : Type} {n : ℕ} (v : α → M)
    (p : Set (L.BoundedFormula α n)) : Prop :=
  ∀ l : List (L.BoundedFormula α n), (∀ φ ∈ l, φ ∈ p) → ∃ x : Fin n → M, ∀ φ ∈ l, φ.Realize v x

def IsSat (M : Type) [L.Structure M] (κ : Cardinal) : Prop :=
  ∀ (α : Type) (v : α → M), Cardinal.mk α < κ →
    ∀ {n : ℕ} (p : Set (L.BoundedFormula α n)), FinSat v p →
      ∃ x : Fin n → M, ∀ φ ∈ p, φ.Realize v x

def PartElem {M : Type} [L.Structure M] {α : Type} (v w : α → M) : Prop :=
  ∀ {n : ℕ} (φ : L.BoundedFormula α n) (a : Fin n → α),
    φ.Realize v (v ∘ a) ↔ φ.Realize w (w ∘ a)

def IsSH (M : Type) [L.Structure M] (κ : Cardinal) : Prop :=
  ∀ (α : Type) (v w : α → M), Cardinal.mk α < κ → PartElem (L := L) v w →
    ∃ e : M ≃[L] M, ∀ a, e (v a) = w a

/-! ## One ultrapower step: realize every type over `M` and extend every
partial elementary map of `M` to an elementary map into the ultrapower. -/

section Step
variable (M : Type) [L.Structure M] [Nonempty M]

abbrev Cond := Σ n : ℕ, L.BoundedFormula M n
abbrev StepIdx := Finset (Cond (L := L) M)

def stepU : Ultrafilter (StepIdx (L := L) M) := Ultrafilter.of Filter.atTop

abbrev Step : Type := ((stepU (L := L) M : Ultrafilter (StepIdx (L := L) M)) : Filter _).Product
  (fun _ : StepIdx (L := L) M => M)

theorem stepU_cone (s₀ : StepIdx (L := L) M) :
    ∀ᶠ s in (stepU (L := L) M : Filter (StepIdx (L := L) M)), s₀ ⊆ s :=
  Ultrafilter.of_le _ (Filter.eventually_ge_atTop s₀)

def diag : M ↪ₑ[L] Step (L := L) M where
  toFun m := ((fun _ => m : StepIdx (L := L) M → M) : Step (L := L) M)
  map_formula' n φ x := by
    have h := Ultraproduct.realize_formula_cast (u := stepU (L := L) M)
      (M := fun _ : StepIdx (L := L) M => M) φ (fun i _ => x i)
    exact h.trans Filter.eventually_const

variable {M}

theorem key_realize {α : Type} (v : α → M) {n : ℕ} (φ ψ : L.BoundedFormula α n)
    (h : (⟨n, φ.subst (fun a => Term.var (v a))⟩ : Cond (L := L) M) =
      ⟨n, ψ.subst (fun a => Term.var (v a))⟩) (x : Fin n → M) :
    φ.Realize v x ↔ ψ.Realize v x := by
  have h' : φ.subst (fun a => Term.var (v a)) = ψ.subst (fun a => Term.var (v a)) :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have h₁ := BoundedFormula.realize_subst (φ := φ) (tf := fun a => Term.var (v a)) (v := id) (xs := x)
  have h₂ := BoundedFormula.realize_subst (φ := ψ) (tf := fun a => Term.var (v a)) (v := id) (xs := x)
  rw [h'] at h₁
  exact h₁.symm.trans h₂

theorem step_finite_part {α : Type} (v : α → M) {n : ℕ} (p : Set (L.BoundedFormula α n))
    (hp : FinSat v p) (s : StepIdx (L := L) M) :
    ∃ x : Fin n → M, ∀ φ ∈ p,
      (⟨n, φ.subst (fun a => Term.var (v a))⟩ : Cond (L := L) M) ∈ s → φ.Realize v x := by
  let key : L.BoundedFormula α n → Cond (L := L) M := fun φ => ⟨n, φ.subst (fun a => Term.var (v a))⟩
  let pick : Cond (L := L) M → Option (L.BoundedFormula α n) := fun k =>
    if h : ∃ φ ∈ p, key φ = k then some (Classical.choose h) else none
  let l := s.toList.filterMap pick
  have hl : ∀ ψ ∈ l, ψ ∈ p := by
    intro ψ hψ
    obtain ⟨k, _, hk⟩ := List.mem_filterMap.mp hψ
    simp only [pick] at hk
    split_ifs at hk with h
    cases hk
    exact (Classical.choose_spec h).1
  obtain ⟨x, hx⟩ := hp l hl
  refine ⟨x, fun φ hφ hs => ?_⟩
  have h : ∃ φ' ∈ p, key φ' = key φ := ⟨φ, hφ, rfl⟩
  have hmem : Classical.choose h ∈ l := by
    refine List.mem_filterMap.mpr ⟨key φ, Finset.mem_toList.mpr hs, ?_⟩
    exact dite_eq_left h
  exact (key_realize v φ (Classical.choose h) (Classical.choose_spec h).2.symm x).mpr (hx _ hmem)

theorem step_realizes {α : Type} (v : α → M) {n : ℕ} (p : Set (L.BoundedFormula α n))
    (hp : FinSat v p) :
    ∃ x : Fin n → Step (L := L) M, ∀ φ ∈ p, φ.Realize (diag (L := L) M ∘ v) x := by
  choose xs hxs using step_finite_part v p hp
  refine ⟨fun i => ((fun s => xs s i : StepIdx (L := L) M → M) : Step (L := L) M), fun φ hφ => ?_⟩
  have h := Ultraproduct.boundedFormula_realize_cast (u := stepU (L := L) M)
    (M := fun _ : StepIdx (L := L) M => M) φ (fun a _ => v a) (fun i s => xs s i)
  refine h.mpr ?_
  filter_upwards [stepU_cone M {⟨n, φ.subst (fun a => Term.var (v a))⟩}] with s hs
  exact hxs s φ hφ (hs (Finset.mem_singleton_self _))


theorem partElem_eq {α : Type} {v w : α → M} (h : PartElem (L := L) v w) {a b : α}
    (hab : v a = v b) : w a = w b := by
  have h' := h (n := 0) ((Term.var (Sum.inl a)).bdEqual (Term.var (Sum.inl b))) Fin.elim0
  simp only [BoundedFormula.realize_bdEqual, Term.realize_var, Sum.elim_inl] at h'
  exact h'.mp hab

theorem partElem_extend_formula {α : Type} (v w : α → M) (h : PartElem (L := L) v w)
    (θ : L.Formula M) (hθ : θ.Realize id) :
    ∃ g : M → M, (∀ a, g (v a) = w a) ∧ θ.Realize g := by
  let F := BoundedFormula.freeVarFinset θ
  let ρ : F → α ⊕ F := fun m =>
    if hm : m.1 ∈ Set.range v then Sum.inl (Classical.choose hm) else Sum.inr m
  let θ' : L.Formula (α ⊕ F) := BoundedFormula.restrictFreeVar θ ρ
  have h1 : θ'.Realize (Sum.elim v Subtype.val) := by
    have hr := BoundedFormula.realize_restrictFreeVar (φ := θ) (f := ρ)
      (v := Sum.elim v Subtype.val) (xs := default) id (by
        intro m
        by_cases hm : m.1 ∈ Set.range v
        · simp only [ρ, dite_eq_left hm, Sum.elim_inl]
          exact Classical.choose_spec hm
        · simp only [ρ, dite_eq_right hm, Sum.elim_inr]
          rfl)
    exact hr.mpr hθ
  have h3 : BoundedFormula.Realize (θ'.iExs F) w (w ∘ Fin.elim0) :=
    (h (n := 0) (θ'.iExs F) Fin.elim0).mp (BoundedFormula.realize_iExs.mpr ⟨_, h1⟩)
  obtain ⟨y, hy⟩ := BoundedFormula.realize_iExs.mp h3
  let g : M → M := fun m =>
    if hm : m ∈ Set.range v then w (Classical.choose hm)
    else if hF : m ∈ F then y ⟨m, hF⟩ else m
  refine ⟨g, fun a => ?_, ?_⟩
  · have hm : v a ∈ Set.range v := ⟨a, rfl⟩
    simp only [g, dite_eq_left hm]
    exact partElem_eq h (Classical.choose_spec hm)
  · have hr := BoundedFormula.realize_restrictFreeVar (φ := θ) (f := ρ)
      (v := Sum.elim w y) (xs := default) g (by
        intro m
        by_cases hm : m.1 ∈ Set.range v
        · simp only [ρ, g, dite_eq_left hm, Sum.elim_inl]
        · simp only [ρ, g, dite_eq_right hm, Sum.elim_inr]
          rw [dite_eq_left (show m.1 ∈ F from m.2)])
    exact hr.mp hy

theorem step_extends {α : Type} (v w : α → M) (h : PartElem (L := L) v w) :
    ∃ g : M ↪ₑ[L] Step (L := L) M, ∀ a, g (v a) = diag (L := L) M (w a) := by
  let s0 : StepIdx (L := L) M → Finset (L.Formula M) := fun s =>
    s.preimage (Sigma.mk 0) (Set.injOn_of_injective sigma_mk_injective)
  let lit : L.Formula M → L.Formula M := fun σ => if σ.Realize id then σ else σ.not
  let θ : StepIdx (L := L) M → L.Formula M := fun s => ((s0 s).toList.map lit).foldr (· ⊓ ·) ⊤
  have hθ : ∀ s, (θ s).Realize id := by
    intro s
    refine (BoundedFormula.realize_foldr_inf _ _ _).mpr ?_
    intro ψ hψ
    obtain ⟨σ, _, rfl⟩ := List.mem_map.mp hψ
    by_cases hσ : σ.Realize id
    · simp only [lit, ite_eq_left hσ]
      exact hσ
    · simp only [lit, ite_eq_right hσ]
      exact BoundedFormula.realize_not.mpr hσ
  choose gs hgs1 hgs2 using fun s => partElem_extend_formula v w h (θ s) (hθ s)
  have hkey : ∀ s (σ : L.Formula M), (⟨0, σ⟩ : Cond (L := L) M) ∈ s →
      (σ.Realize (gs s) ↔ σ.Realize id) := by
    intro s σ hσs
    have hmem : σ ∈ s0 s := Finset.mem_preimage.mpr hσs
    have hl := (BoundedFormula.realize_foldr_inf _ _ _).mp (hgs2 s) (lit σ)
      (List.mem_map.mpr ⟨σ, Finset.mem_toList.mpr hmem, rfl⟩)
    by_cases hσ : σ.Realize id
    · simp only [lit, ite_eq_left hσ] at hl
      exact ⟨fun _ => hσ, fun _ => hl⟩
    · simp only [lit, ite_eq_right hσ] at hl
      exact ⟨fun h' => absurd h' (BoundedFormula.realize_not.mp hl), fun h' => absurd h' hσ⟩
  let G : M → Step (L := L) M := fun m => ((fun s => gs s m : StepIdx (L := L) M → M) : Step (L := L) M)
  refine ⟨⟨G, ?_⟩, fun a => ?_⟩
  · intro n φ x
    have hc := Ultraproduct.realize_formula_cast (u := stepU (L := L) M)
      (M := fun _ : StepIdx (L := L) M => M) φ (fun i s => gs s (x i))
    let σ : L.Formula M := BoundedFormula.subst φ (fun i => Term.var (x i))
    have hσ : ∀ g : M → M, σ.Realize g ↔ φ.Realize (g ∘ x) := fun g =>
      BoundedFormula.realize_subst (φ := φ) (tf := fun i => Term.var (x i)) (v := g) (xs := default)
    change φ.Realize (fun i => G (x i)) ↔ _
    refine hc.trans ⟨fun hev => ?_, fun hφ => ?_⟩
    · obtain ⟨s, hs1, hs2⟩ := (hev.and (stepU_cone M {⟨0, σ⟩})).exists
      exact (hσ id).mp ((hkey s σ (hs2 (Finset.mem_singleton_self _))).mp ((hσ (gs s)).mpr hs1))
    · filter_upwards [stepU_cone M {⟨0, σ⟩}] with s hs
      exact (hσ (gs s)).mp ((hkey s σ (hs (Finset.mem_singleton_self _))).mpr ((hσ id).mpr hφ))
  · change ((fun s => gs s (v a) : StepIdx (L := L) M → M) : Step (L := L) M) =
      ((fun _ => w a : StepIdx (L := L) M → M) : Step (L := L) M)
    exact congrArg _ (funext fun s => hgs1 s a)

end Step



/-! ## The category of `L`-structures and elementary embeddings, with
colimits of directed diagrams given by direct limits -/

structure EObj (L : FirstOrder.Language.{0, 0}) : Type 1 where
  carrier : Type
  [str : L.Structure carrier]
  [ne : Nonempty carrier]

attribute [instance] EObj.str EObj.ne

open CategoryTheory CategoryTheory.Limits

instance : Category (EObj L) where
  Hom X Y := X.carrier ↪ₑ[L] Y.carrier
  id X := ElementaryEmbedding.refl L X.carrier
  comp f g := g.comp f
  id_comp _ := ElementaryEmbedding.ext fun _ => rfl
  comp_id _ := ElementaryEmbedding.ext fun _ => rfl
  assoc _ _ _ := ElementaryEmbedding.ext fun _ => rfl

def toE {X Y : EObj L} (f : X ⟶ Y) : X.carrier ↪ₑ[L] Y.carrier := f
def ofE {X Y : EObj L} (f : X.carrier ↪ₑ[L] Y.carrier) : X ⟶ Y := f

@[simp] theorem toE_comp {X Y Z : EObj L} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.carrier) :
    toE (f ≫ g) x = toE g (toE f x) := rfl
@[simp] theorem toE_id (X : EObj L) (x : X.carrier) : toE (𝟙 X) x = x := rfl
@[simp] theorem toE_ofE {X Y : EObj L} (f : X.carrier ↪ₑ[L] Y.carrier) (x : X.carrier) :
    toE (ofE f) x = f x := rfl

theorem hom_ext {X Y : EObj L} {f g : X ⟶ Y} (h : ∀ x, toE f x = toE g x) : f = g :=
  ElementaryEmbedding.ext h

section Colim
variable {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (F : ι ⥤ EObj L)

abbrev sysG (i : ι) : Type := (F.obj i).carrier

def sysF (i j : ι) (h : i ≤ j) : sysG F i ↪[L] sysG F j := (toE (F.map (homOfLE h))).toEmbedding

theorem sysF_apply (i j : ι) (h : i ≤ j) (x : sysG F i) :
    sysF F i j h x = toE (F.map (homOfLE h)) x := rfl

theorem toE_map_apply {i j : ι} (h : i ⟶ j) (x : sysG F i) :
    toE (F.map h) x = sysF F i j (leOfHom h) x := by
  rw [sysF_apply]
  exact congrArg (fun m => toE (F.map m) x) (Subsingleton.elim _ _)

instance sysF_directed : DirectedSystem (sysG F) (fun i j h => sysF F i j h) where
  map_self i x := by
    change toE (F.map (homOfLE (le_refl i))) x = x
    rw [show homOfLE (le_refl i) = 𝟙 i from Subsingleton.elim _ _, F.map_id]
    rfl
  map_map k j i hij hjk x := by
    change toE (F.map (homOfLE hjk)) (toE (F.map (homOfLE hij)) x) =
      toE (F.map (homOfLE (hij.trans hjk))) x
    rw [← toE_comp, ← F.map_comp]
    rfl

abbrev Lim : Type := FirstOrder.Language.DirectLimit (sysG F) (sysF F)

def limOf (i : ι) : sysG F i ↪[L] Lim F := FirstOrder.Language.DirectLimit.of L ι (sysG F) (sysF F) i

instance : Nonempty (Lim F) :=
  ⟨limOf F (Classical.arbitrary ι) (Classical.arbitrary _)⟩

theorem limOf_f {i j : ι} (h : i ≤ j) (x : sysG F i) : limOf F j (sysF F i j h x) = limOf F i x :=
  FirstOrder.Language.DirectLimit.of_f

theorem lim_realize {β : Type} {n : ℕ} (φ : L.BoundedFormula β n) :
    ∀ (i : ι) (v : β → sysG F i) (xs : Fin n → sysG F i),
      φ.Realize (limOf F i ∘ v) (limOf F i ∘ xs) ↔ φ.Realize v xs := by
  induction φ with
  | falsum => intros; rfl
  | equal t₁ t₂ =>
    intro i v xs
    simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
    exact (limOf F i).injective.eq_iff
  | rel R ts =>
    intro i v xs
    simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
    exact (limOf F i).map_rel R _
  | imp φ ψ ih₁ ih₂ =>
    intro i v xs
    simp only [BoundedFormula.Realize]
    rw [ih₁, ih₂]
  | all φ ih =>
    intro i v xs
    simp only [BoundedFormula.realize_all]
    constructor
    · intro h x
      have h' := h (limOf F i x)
      rw [← Fin.comp_snoc] at h'
      exact (ih i v (Fin.snoc xs x)).mp h'
    · intro h y
      obtain ⟨j, z, rfl⟩ := FirstOrder.Language.DirectLimit.exists_of y
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      let g := toE (F.map (homOfLE hik))
      have hall : (∀' φ).Realize (g ∘ v) (g ∘ xs) :=
        (g.map_boundedFormula (∀' φ) v xs).mpr (BoundedFormula.realize_all.mpr h)
      have h2 := BoundedFormula.realize_all.mp hall (sysF F j k hjk z)
      have h3 := (ih k (g ∘ v) (Fin.snoc (g ∘ xs) (sysF F j k hjk z))).mpr h2
      have e1 : limOf F k ∘ (g ∘ v) = limOf F i ∘ v :=
        funext fun b => limOf_f F hik (v b)
      have e2 : limOf F k ∘ Fin.snoc (g ∘ xs) (sysF F j k hjk z) =
          Fin.snoc (limOf F i ∘ xs) (FirstOrder.Language.DirectLimit.of L ι (sysG F) (sysF F) j z) := by
        rw [Fin.comp_snoc]
        congr 1
        · exact funext fun b => limOf_f F hik (xs b)
        · exact limOf_f F hjk z
      rw [e1, e2] at h3
      exact h3

theorem lim_formula {β : Type} (φ : L.Formula β) (i : ι) (v : β → sysG F i) :
    φ.Realize (limOf F i ∘ v) ↔ φ.Realize v := by
  unfold Formula.Realize
  rw [show (default : Fin 0 → Lim F) = limOf F i ∘ default from Subsingleton.elim _ _]
  exact lim_realize F φ i v default

def limOfE (i : ι) : sysG F i ↪ₑ[L] Lim F where
  toFun := limOf F i
  map_formula' _ φ x := lim_formula F φ i x

@[simp] theorem limOfE_apply (i : ι) (x : sysG F i) : limOfE F i x = limOf F i x := rfl

theorem lim_exists (z : Lim F) : ∃ i x, limOf F i x = z := FirstOrder.Language.DirectLimit.exists_of z

def limCocone : Cocone F where
  pt := ⟨Lim F⟩
  ι :=
    { app := fun i => ofE (limOfE F i)
      naturality := fun i j h => hom_ext fun x => by
        change limOf F j (toE (F.map h) x) = limOf F i x
        rw [toE_map_apply]
        exact limOf_f F _ x }

def limDescEmb (s : Cocone F) : Lim F ↪[L] s.pt.carrier :=
  FirstOrder.Language.DirectLimit.lift L ι (sysG F) (sysF F) (fun i => (toE (s.ι.app i)).toEmbedding)
    (fun i j hij x => by
      have h := congrArg (fun m => toE m x) (s.w (homOfLE hij))
      exact h)

theorem limDescEmb_of (s : Cocone F) (i : ι) (x : sysG F i) :
    limDescEmb F s (limOf F i x) = toE (s.ι.app i) x :=
  FirstOrder.Language.DirectLimit.lift_of _ _ x

def limDesc (s : Cocone F) : (⟨Lim F⟩ : EObj L) ⟶ s.pt := ofE
  { toFun := limDescEmb F s
    map_formula' := fun _ φ x => by
      obtain ⟨i, y, hy⟩ := FirstOrder.Language.DirectLimit.exists_quotient_mk'_sigma_mk'_eq (sysG F) (sysF F) x
      have hx : x = limOf F i ∘ y := hy
      subst hx
      have hc : limDescEmb F s ∘ (limOf F i ∘ y) = toE (s.ι.app i) ∘ y :=
        funext fun a => limDescEmb_of F s i (y a)
      rw [hc, (toE (s.ι.app i)).map_formula, lim_formula] }

def limIsColimit : IsColimit (limCocone F) where
  desc := limDesc F
  fac s i := hom_ext fun x => limDescEmb_of F s i x
  uniq s m hm := hom_ext fun x => by
    obtain ⟨i, y, rfl⟩ := lim_exists F x
    have h := congrArg (fun f => toE f y) (hm i)
    change toE m (limOf F i y) = toE (s.ι.app i) y at h
    change toE m (limOf F i y) = limDescEmb F s (limOf F i y)
    rw [h, limDescEmb_of]

instance hasColimitsOfShape_directed : HasColimitsOfShape ι (EObj L) :=
  ⟨fun F => HasColimit.mk ⟨limCocone F, limIsColimit F⟩⟩

end Colim


/-! ## Partial elementary relations -/

section PE
variable {N : Type} [L.Structure N]

/-- A relation all of whose finite tuples of pairs are elementary. -/
def PE (R : Set (N × N)) : Prop :=
  ∀ {n : ℕ} (φ : L.Formula (Fin n)) (x : Fin n → N × N), (∀ i, x i ∈ R) →
    (φ.Realize (Prod.fst ∘ x) ↔ φ.Realize (Prod.snd ∘ x))

theorem PE.functional {R : Set (N × N)} (h : PE (L := L) R) {a b b' : N}
    (hb : (a, b) ∈ R) (hb' : (a, b') ∈ R) : b = b' := by
  have h' := h (n := 2) ((Term.var 0).equal (Term.var 1)) ![(a, b), (a, b')]
    (by intro i; fin_cases i <;> assumption)
  simp only [Formula.realize_equal, Term.realize_var] at h'
  exact h'.mp rfl

theorem PE.mono {R S : Set (N × N)} (h : PE (L := L) S) (hRS : R ⊆ S) : PE (L := L) R :=
  fun φ x hx => h φ x (fun i => hRS (hx i))

theorem PE_range_pair {Z : Type} [L.Structure Z] (h₁ h₂ : Z ↪ₑ[L] N) :
    PE (L := L) (Set.range fun z => (h₁ z, h₂ z)) := by
  intro n φ x hx
  choose z hz using hx
  have e₁ : Prod.fst ∘ x = h₁ ∘ z := funext fun i => by rw [Function.comp_apply, ← hz i]; rfl
  have e₂ : Prod.snd ∘ x = h₂ ∘ z := funext fun i => by rw [Function.comp_apply, ← hz i]; rfl
  rw [e₁, e₂, h₁.map_formula, h₂.map_formula]

theorem PE_image {X : Type} [L.Structure X] (h : X ↪ₑ[L] N) {R : Set (X × X)} (hR : PE (L := L) R) :
    PE (L := L) ((fun q : X × X => (h q.1, h q.2)) '' R) := by
  intro n φ x hx
  choose q hq hqx using hx
  have e₁ : Prod.fst ∘ x = h ∘ (Prod.fst ∘ q) := funext fun i => by simp [← hqx i]
  have e₂ : Prod.snd ∘ x = h ∘ (Prod.snd ∘ q) := funext fun i => by simp [← hqx i]
  rw [e₁, e₂, h.map_formula, h.map_formula]
  exact hR φ q hq

theorem PE_preimage {X : Type} [L.Structure X] (h : X ↪ₑ[L] N) {R : Set (N × N)} (hR : PE (L := L) R) :
    PE (L := L) {q : X × X | (h q.1, h q.2) ∈ R} := by
  intro n φ x hx
  have := hR φ (fun i => (h (x i).1, h (x i).2)) hx
  rw [← h.map_formula φ, ← h.map_formula φ]
  exact this

theorem PE_of_partElem {α : Type} {v w : α → N} (h : PartElem (L := L) v w) :
    PE (L := L) (Set.range fun a => (v a, w a)) := by
  intro n φ x hx
  choose a ha using hx
  have e₁ : Prod.fst ∘ x = v ∘ a := funext fun i => by rw [Function.comp_apply, ← ha i]; rfl
  have e₂ : Prod.snd ∘ x = w ∘ a := funext fun i => by rw [Function.comp_apply, ← ha i]; rfl
  rw [e₁, e₂]
  have h' := h (n := 0) (φ.relabel a) Fin.elim0
  rw [show (v ∘ Fin.elim0 : Fin 0 → N) = default from Subsingleton.elim _ _,
    show (w ∘ Fin.elim0 : Fin 0 → N) = default from Subsingleton.elim _ _] at h'
  exact Formula.realize_relabel.symm.trans (h'.trans Formula.realize_relabel)

theorem PE_formula {R : Set (N × N)} (h : PE (L := L) R) (ψ : L.Formula R) :
    ψ.Realize (fun r => r.1.1) ↔ ψ.Realize (fun r => r.1.2) := by
  let s := BoundedFormula.freeVarFinset ψ
  let e := s.equivFin
  let ψ' : L.Formula (Fin s.card) := BoundedFormula.restrictFreeVar ψ (fun r => e r)
  let x : Fin s.card → N × N := fun k => (e.symm k).1.1
  have hx : ∀ k, x k ∈ R := fun k => (e.symm k).1.2
  have h₁ : ψ'.Realize (Prod.fst ∘ x) ↔ ψ.Realize (fun r => r.1.1) :=
    BoundedFormula.realize_restrictFreeVar _ (fun r => by simp [x])
  have h₂ : ψ'.Realize (Prod.snd ∘ x) ↔ ψ.Realize (fun r => r.1.2) :=
    BoundedFormula.realize_restrictFreeVar _ (fun r => by simp [x])
  exact h₁.symm.trans ((h ψ' x hx).trans h₂)

theorem partElem_of_PE {R : Set (N × N)} (h : PE (L := L) R) :
    PartElem (L := L) (fun r : R => r.1.1) (fun r : R => r.1.2) := by
  intro n φ a
  let ψ : L.Formula R := (BoundedFormula.toFormula φ).relabel (Sum.elim id a)
  have hψ : ∀ u : R → N, ψ.Realize u ↔ φ.Realize u (u ∘ a) := fun u => by
    rw [Formula.realize_relabel, BoundedFormula.realize_toFormula]
    rfl
  exact (hψ _).symm.trans ((PE_formula h ψ).trans (hψ _))

/-- Finite families from a chain have an upper bound in the chain. -/
theorem chain_bound {β : Type} [Preorder β] {c : Set β} (hc : IsChain (· ≤ ·) c) (b₀ : β)
    (hb₀ : b₀ ∈ c) : ∀ {n : ℕ} (x : Fin n → β), (∀ i, x i ∈ c) → ∃ m ∈ c, b₀ ≤ m ∧ ∀ i, x i ≤ m
  | 0, _, _ => ⟨b₀, hb₀, le_rfl, fun i => i.elim0⟩
  | n + 1, x, hx => by
    obtain ⟨m, hm, hbm, hxm⟩ := chain_bound hc b₀ hb₀ (fun i : Fin n => x i.castSucc) (fun i => hx _)
    rcases hc.total hm (hx (Fin.last n)) with h | h
    · refine ⟨x (Fin.last n), hx _, hbm.trans h, fun i => ?_⟩
      refine Fin.lastCases le_rfl (fun j => (hxm j).trans h) i
    · exact ⟨m, hm, hbm, fun i => Fin.lastCases h (fun j => hxm j) i⟩

end PE

/-! ## Two ultrapower steps extend a partial elementary map on both sides -/

section TwoStep
variable (X : Type) [L.Structure X] [Nonempty X]

abbrev Step2 : Type := Step (L := L) (Step (L := L) X)

def toStep2 : X ↪ₑ[L] Step2 (L := L) X :=
  (diag (L := L) (Step (L := L) X)).comp (diag (L := L) X)

theorem step2_extend (R : Set (X × X)) (hR : PE (L := L) R) :
    ∃ R' : Set (Step2 (L := L) X × Step2 (L := L) X), PE (L := L) R' ∧
      (∀ q ∈ R, (toStep2 X q.1, toStep2 X q.2) ∈ R') ∧
      ∀ x, (∃ b, (toStep2 X x, b) ∈ R') ∧ (∃ a, (a, toStep2 X x) ∈ R') := by
  obtain ⟨g₁, hg₁⟩ := step_extends (L := L) (fun r : R => r.1.1) (fun r : R => r.1.2) (partElem_of_PE hR)
  let R₁ : Set (Step (L := L) X × Step (L := L) X) := Set.range fun x => (g₁ x, diag (L := L) X x)
  obtain ⟨g₂, hg₂⟩ := step_extends (L := L) (fun r : R₁ => r.1.1) (fun r : R₁ => r.1.2)
    (partElem_of_PE (PE_range_pair g₁ (diag (L := L) X)))
  have hg₂' : ∀ x, g₂ (g₁ x) = diag (L := L) _ (diag (L := L) X x) := fun x =>
    hg₂ ⟨(g₁ x, diag (L := L) X x), x, rfl⟩
  refine ⟨Set.range fun y => (g₂ y, diag (L := L) _ y), PE_range_pair g₂ (diag (L := L) _), ?_, ?_⟩
  · intro q hq
    have h1 : g₁ q.1 = diag (L := L) X q.2 := hg₁ ⟨q, hq⟩
    refine ⟨diag (L := L) X q.2, Prod.ext ?_ rfl⟩
    change g₂ (diag (L := L) X q.2) = diag (L := L) _ (diag (L := L) X q.1)
    rw [← h1, hg₂']
  · intro x
    exact ⟨⟨_, g₁ x, Prod.ext (hg₂' x) rfl⟩, ⟨_, diag (L := L) X x, rfl⟩⟩

end TwoStep


/-! ## The transfinite chain of length `κ` and its union -/

section Chain
variable (κ : Cardinal.{0}) [hκ : Fact κ.IsRegular]

instance J_nonempty : Nonempty κ.ord.ToType :=
  Ordinal.nonempty_toType_iff.mpr hκ.out.ord_pos.ne'

instance J_orderBot : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _

theorem J_not_isMax (j : κ.ord.ToType) : ¬ IsMax j := by
  intro hmax
  have hlim : Order.IsSuccLimit κ.ord := Cardinal.isSuccLimit_ord hκ.out.aleph0_le
  let o : Set.Iio κ.ord := Ordinal.ToType.mk.symm j
  have hs : Order.succ o.1 < κ.ord := hlim.succ_lt o.2
  have hlt : o < ⟨Order.succ o.1, hs⟩ := Subtype.mk_lt_mk.mpr (Order.lt_succ o.1)
  have h2 : Ordinal.ToType.mk o < Ordinal.ToType.mk ⟨Order.succ o.1, hs⟩ :=
    Ordinal.ToType.mk.strictMono hlt
  rw [show Ordinal.ToType.mk o = j from Ordinal.ToType.mk.apply_symm_apply j] at h2
  exact hmax.not_lt h2

theorem J_bounded {α : Type} (hα : Cardinal.mk α < κ) (i : α → κ.ord.ToType) :
    ∃ j, ∀ a, i a ≤ j := by
  by_contra hcon
  simp only [not_exists, not_forall, not_le] at hcon
  have hcover : (Set.univ : Set κ.ord.ToType) = ⋃ a, Set.Iio (i a) := by
    ext j
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_Iio, true_iff]
    obtain ⟨a, ha⟩ := hcon j
    exact ⟨a, ha⟩
  have hsmall : ∀ a, Cardinal.mk (Set.Iio (i a)) < κ := fun a => by
    have h := Cardinal.mk_Iio_lt (i a) (by rw [Cardinal.mk_ord_toType, Ordinal.type_toType])
    rwa [Cardinal.mk_ord_toType] at h
  have h := (Cardinal.card_iUnion_lt_iff_forall_of_isRegular hκ.out hα).mpr hsmall
  rw [← hcover, Cardinal.mk_univ, Cardinal.mk_ord_toType] at h
  exact lt_irrefl _ h

instance : HasIterationOfShape κ.ord.ToType (EObj L) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have : Nonempty (Set.Iio j) := by
      obtain ⟨b, hb⟩ := not_isMin_iff.mp hj.not_isMin
      exact ⟨⟨b, hb⟩⟩
    infer_instance
  hasColimitsOfShape := inferInstance

variable (M : Type) [L.Structure M] [Nonempty M]

def succObj (X : EObj L) : EObj L := ⟨Step2 (L := L) X.carrier⟩

def succStr : SmallObject.SuccStruct (EObj L) where
  X₀ := ⟨M⟩
  succ := succObj
  toSucc X := ofE (toStep2 (L := L) X.carrier)

abbrev chain : κ.ord.ToType ⥤ EObj L := (succStr (L := L) M).iterationFunctor κ.ord.ToType

/-- The union of the chain; `mon_sat` and `mon_sh` prove it is a monster model. -/
abbrev Mon : Type := Lim (chain (L := L) κ M)

def baseE : M ↪ₑ[L] Mon (L := L) κ M :=
  (limOfE (chain (L := L) κ M) ⊥).comp
    (toE ((succStr (L := L) M).iterationFunctorObjBotIso κ.ord.ToType).inv)

def nextE (j : κ.ord.ToType) :
    Step2 (L := L) ((chain (L := L) κ M).obj j).carrier ↪ₑ[L] Mon (L := L) κ M :=
  (limOfE (chain (L := L) κ M) (Order.succ j)).comp
    (toE ((succStr (L := L) M).iterationFunctorObjSuccIso j (J_not_isMax κ j)).inv)

theorem nextE_toStep2 (j : κ.ord.ToType) (x : ((chain (L := L) κ M).obj j).carrier) :
    nextE κ M j (toStep2 (L := L) _ x) = limOf (chain (L := L) κ M) j x := by
  have h := (succStr (L := L) M).iterationFunctor_map_succ j (J_not_isMax κ j)
  have h' := congrArg (fun m => toE m x) h
  change toE ((chain (L := L) κ M).map (homOfLE (Order.le_succ j))) x =
    toE ((succStr (L := L) M).iterationFunctorObjSuccIso j (J_not_isMax κ j)).inv
      (toStep2 (L := L) _ x) at h'
  change limOf (chain (L := L) κ M) (Order.succ j)
      (toE ((succStr (L := L) M).iterationFunctorObjSuccIso j (J_not_isMax κ j)).inv
        (toStep2 (L := L) _ x)) = _
  rw [← h', toE_map_apply, limOf_f]

theorem nextE_mem (j : κ.ord.ToType) (y : Step2 (L := L) ((chain (L := L) κ M).obj j).carrier) :
    nextE κ M j y ∈ Set.range (limOf (chain (L := L) κ M) (Order.succ j)) :=
  ⟨_, rfl⟩

/-- Saturation of the union. -/
theorem mon_sat : IsSat (L := L) (Mon (L := L) κ M) κ := by
  intro α v hα n p hp
  choose i y hy using fun a => lim_exists (chain (L := L) κ M) (v a)
  obtain ⟨j, hj⟩ := J_bounded κ hα i
  let G := ((chain (L := L) κ M).obj j).carrier
  let v' : α → G := fun a => sysF (chain (L := L) κ M) (i a) j (hj a) (y a)
  have hv' : limOf (chain (L := L) κ M) j ∘ v' = v :=
    funext fun a => (limOf_f _ (hj a) (y a)).trans (hy a)
  have hp' : FinSat v' p := by
    intro l hl
    obtain ⟨x, hx⟩ := hp l hl
    let θ : L.Formula α := BoundedFormula.exs (l.foldr (· ⊓ ·) ⊤)
    have hθ : θ.Realize v :=
      BoundedFormula.realize_exs.mpr ⟨x, (BoundedFormula.realize_foldr_inf _ _ _).mpr hx⟩
    rw [← hv'] at hθ
    obtain ⟨x', hx'⟩ := BoundedFormula.realize_exs.mp ((lim_formula _ θ j v').mp hθ)
    exact ⟨x', (BoundedFormula.realize_foldr_inf _ _ _).mp hx'⟩
  obtain ⟨x₁, hx₁⟩ := step_realizes (L := L) v' p hp'
  let h := (nextE κ M j).comp (diag (L := L) (Step (L := L) G))
  refine ⟨h ∘ x₁, fun φ hφ => ?_⟩
  have hcomp : h ∘ (diag (L := L) G ∘ v') = v := by
    rw [← hv']
    funext a
    exact nextE_toStep2 κ M j (v' a)
  rw [← hcomp]
  exact (h.map_boundedFormula φ _ x₁).mpr (hx₁ φ hφ)


/-- Strong homogeneity of the union, by Zorn's lemma on partial elementary
relations carrying a stage bookkeeping index. -/
theorem mon_sh : IsSH (L := L) (Mon (L := L) κ M) κ := by
  intro α v w hα hvw
  let C := chain (L := L) κ M
  let N := Mon (L := L) κ M
  let stage : κ.ord.ToType → Set N := fun j => Set.range (limOf C j)
  have stage_mono : ∀ {i j : κ.ord.ToType}, i ≤ j → stage i ⊆ stage j := by
    rintro i j hij _ ⟨y, rfl⟩
    exact ⟨sysF C i j hij y, limOf_f C hij y⟩
  have stage_cover : ∀ z : N, ∃ j, z ∈ stage j := fun z => by
    obtain ⟨j, x, hx⟩ := lim_exists C z
    exact ⟨j, x, hx⟩
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : κ.ord.ToType, ∀ a, v a ∈ stage δ₀ ∧ w a ∈ stage δ₀ := by
    choose iv hiv using fun a => stage_cover (v a)
    choose iw hiw using fun a => stage_cover (w a)
    have hα2 : Cardinal.mk (α ⊕ α) < κ := by
      rw [Cardinal.mk_sum, Cardinal.lift_id]
      exact Cardinal.add_lt_of_lt hκ.out.aleph0_le hα hα
    obtain ⟨j, hj⟩ := J_bounded κ hα2 (Sum.elim iv iw)
    exact ⟨j, fun a => ⟨stage_mono (hj (Sum.inl a)) (hiv a), stage_mono (hj (Sum.inr a)) (hiw a)⟩⟩
  let f₀ : Set (N × N) := Set.range fun a => (v a, w a)
  have hf₀ : PE (L := L) f₀ := PE_of_partElem hvw
  let Good : Set (Set (N × N) × WithTop κ.ord.ToType) := {p |
    f₀ ⊆ p.1 ∧ PE (L := L) p.1 ∧
    (∀ γ : κ.ord.ToType, (γ : WithTop κ.ord.ToType) < p.2 → ∀ z ∈ stage γ,
      (∃ b, (z, b) ∈ p.1) ∧ (∃ a, (a, z) ∈ p.1)) ∧
    (∀ γ : κ.ord.ToType, p.2 = γ → ∀ q ∈ p.1, q.1 ∈ stage (γ ⊔ δ₀) ∧ q.2 ∈ stage (γ ⊔ δ₀))}
  have hub : ∀ c ⊆ Good, IsChain (· ≤ ·) c → ∃ ub ∈ Good, ∀ z ∈ c, z ≤ ub := by
    intro c hcG hc
    let D : Set (WithTop κ.ord.ToType) := Prod.snd '' c
    let UB : Set κ.ord.ToType := {j | ∀ d ∈ D, d ≤ (j : WithTop κ.ord.ToType)}
    let δs : WithTop κ.ord.ToType :=
      if h : UB.Nonempty then ((wellFounded_lt.min UB h : κ.ord.ToType) : WithTop κ.ord.ToType) else ⊤
    have P1 : ∀ p ∈ c, p.2 ≤ δs := by
      intro p hp
      by_cases h : UB.Nonempty
      · simp only [δs, dite_eq_left h]
        exact wellFounded_lt.min_mem UB h p.2 ⟨p, hp, rfl⟩
      · simp only [δs, dite_eq_right h]
        exact le_top
    have P2 : ∀ γ : κ.ord.ToType, (γ : WithTop κ.ord.ToType) < δs →
        ∃ p ∈ c, (γ : WithTop κ.ord.ToType) < p.2 := by
      intro γ hγ
      have hγUB : γ ∉ UB := by
        intro hγ'
        by_cases h : UB.Nonempty
        · simp only [δs, dite_eq_left h, WithTop.coe_lt_coe] at hγ
          exact wellFounded_lt.not_lt_min UB hγ' hγ
        · exact h ⟨γ, hγ'⟩
      simp only [UB, Set.mem_ofPred_eq, not_forall, not_le] at hγUB
      obtain ⟨d, ⟨p, hp, rfl⟩, hd⟩ := hγUB
      exact ⟨p, hp, hd⟩
    let U : Set (N × N) := f₀ ∪ ⋃ p ∈ c, p.1
    refine ⟨(U, δs), ⟨Set.subset_union_left, ?_, ?_, ?_⟩, fun p hp =>
      ⟨Set.subset_union_of_subset_right (Set.subset_biUnion_of_mem (u := fun p => p.1) hp) _,
        P1 p hp⟩⟩
    · intro n φ x hx
      by_cases hne : c.Nonempty
      · obtain ⟨p₀, hp₀⟩ := hne
        have hx' : ∀ i, ∃ p ∈ c, x i ∈ p.1 := by
          intro i
          rcases hx i with h | h
          · exact ⟨p₀, hp₀, (hcG hp₀).1 h⟩
          · obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp h
            exact ⟨p, hp, hxp⟩
        choose P hP hxP using hx'
        obtain ⟨m, hm, -, hPm⟩ := chain_bound hc p₀ hp₀ P hP
        exact (hcG hm).2.1 φ x (fun i => (hPm i).1 (hxP i))
      · have hc0 : c = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        refine hf₀ φ x (fun i => ?_)
        rcases hx i with h | h
        · exact h
        · obtain ⟨p, hp, -⟩ := Set.mem_iUnion₂.mp h
          rw [hc0] at hp
          exact hp.elim
    · intro γ hγ z hz
      obtain ⟨p, hp, hγp⟩ := P2 γ hγ
      obtain ⟨⟨b, hb⟩, ⟨a, ha⟩⟩ := (hcG hp).2.2.1 γ hγp z hz
      exact ⟨⟨b, Or.inr (Set.mem_iUnion₂.mpr ⟨p, hp, hb⟩)⟩,
        ⟨a, Or.inr (Set.mem_iUnion₂.mpr ⟨p, hp, ha⟩)⟩⟩
    · intro γ hγ q hq
      rcases hq with ⟨a, rfl⟩ | hq
      · exact ⟨stage_mono le_sup_right (hδ₀ a).1, stage_mono le_sup_right (hδ₀ a).2⟩
      · obtain ⟨p, hp, hqp⟩ := Set.mem_iUnion₂.mp hq
        have hp2 := P1 p hp
        change δs = _ at hγ
        rw [hγ] at hp2
        cases hpc : p.2 with
        | top => rw [hpc] at hp2; exact absurd hp2 (by simp)
        | coe γ' =>
          rw [hpc, WithTop.coe_le_coe] at hp2
          obtain ⟨h1, h2⟩ := (hcG hp).2.2.2 γ' hpc q hqp
          exact ⟨stage_mono (sup_le_sup_right hp2 _) h1, stage_mono (sup_le_sup_right hp2 _) h2⟩
  obtain ⟨m, hm⟩ := zorn_le₀ Good hub
  obtain ⟨⟨hm1, hm2, hm3, hm4⟩, hmax⟩ := hm
  have htop : m.2 = ⊤ := by
    by_contra hne
    obtain ⟨δ₁, hδ₁⟩ := WithTop.ne_top_iff_exists.mp hne
    let ε : κ.ord.ToType := δ₁ ⊔ δ₀
    let G := (C.obj ε).carrier
    let R₀ : Set (G × G) := {q | (limOf C ε q.1, limOf C ε q.2) ∈ m.1}
    have hR₀ : PE (L := L) R₀ := PE_preimage (limOfE C ε) hm2
    obtain ⟨R'', hR''1, hR''2, hR''3⟩ := step2_extend (L := L) G R₀ hR₀
    let R' : Set (N × N) := (fun q => (nextE κ M ε q.1, nextE κ M ε q.2)) '' R''
    have hmR' : m.1 ⊆ R' := by
      intro q hq
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hm4 δ₁ hδ₁.symm q hq
      have hab : (a, b) ∈ R₀ := by
        change (limOf C ε a, limOf C ε b) ∈ m.1
        rw [ha, hb]
        exact hq
      refine ⟨_, hR''2 (a, b) hab, ?_⟩
      change (nextE κ M ε (toStep2 (L := L) G a), nextE κ M ε (toStep2 (L := L) G b)) = q
      rw [nextE_toStep2, nextE_toStep2, ha, hb]
    have hgood : (R', ((Order.succ ε : κ.ord.ToType) : WithTop κ.ord.ToType)) ∈ Good := by
      refine ⟨hm1.trans hmR', PE_image (nextE κ M ε) hR''1, ?_, ?_⟩
      · intro γ hγ z hz
        rw [WithTop.coe_lt_coe] at hγ
        have hγε : γ ≤ ε := Order.le_of_lt_succ hγ
        obtain ⟨x, rfl⟩ := stage_mono hγε hz
        obtain ⟨⟨b, hb⟩, ⟨a, ha⟩⟩ := hR''3 x
        refine ⟨⟨nextE κ M ε b, _, hb, ?_⟩, ⟨nextE κ M ε a, _, ha, ?_⟩⟩
        · change (nextE κ M ε (toStep2 (L := L) G x), _) = _
          rw [nextE_toStep2]
        · change (_, nextE κ M ε (toStep2 (L := L) G x)) = _
          rw [nextE_toStep2]
      · intro γ hγ q hq
        rw [WithTop.coe_inj] at hγ
        subst hγ
        obtain ⟨y, -, rfl⟩ := hq
        exact ⟨stage_mono le_sup_left (nextE_mem κ M ε y.1),
          stage_mono le_sup_left (nextE_mem κ M ε y.2)⟩
    have hle : m ≤ (R', ((Order.succ ε : κ.ord.ToType) : WithTop κ.ord.ToType)) := by
      refine ⟨hmR', ?_⟩
      rw [← hδ₁, WithTop.coe_le_coe]
      exact le_sup_left.trans (Order.le_succ ε)
    have hge := (hmax hgood hle).2
    change ((Order.succ ε : κ.ord.ToType) : WithTop κ.ord.ToType) ≤ m.2 at hge
    rw [← hδ₁, WithTop.coe_le_coe] at hge
    exact absurd (lt_of_lt_of_le (Order.lt_succ_of_not_isMax (J_not_isMax κ ε)) hge)
      (not_lt.mpr le_sup_left)
  have total : ∀ z : N, ∃ b, (z, b) ∈ m.1 := fun z => by
    obtain ⟨γ, hγ⟩ := stage_cover z
    exact (hm3 γ (htop ▸ WithTop.coe_lt_top γ) z hγ).1
  have surj : ∀ z : N, ∃ a, (a, z) ∈ m.1 := fun z => by
    obtain ⟨γ, hγ⟩ := stage_cover z
    exact (hm3 γ (htop ▸ WithTop.coe_lt_top γ) z hγ).2
  choose g hg using total
  have hgE : ∀ ⦃n : ℕ⦄ (φ : L.Formula (Fin n)) (x : Fin n → N), φ.Realize (g ∘ x) ↔ φ.Realize x :=
    fun n φ x => (hm2 φ (fun i => (x i, g (x i))) (fun i => hg (x i))).symm
  let gE : N ↪ₑ[L] N := ⟨g, hgE⟩
  have hsurj : Function.Surjective g := fun z => by
    obtain ⟨a, ha⟩ := surj z
    exact ⟨a, PE.functional hm2 (hg a) ha⟩
  refine ⟨{ toEquiv := Equiv.ofBijective g ⟨gE.injective, hsurj⟩
            map_fun' := fun f x => gE.map_fun f x
            map_rel' := fun r x => gE.map_rel r x }, fun a => ?_⟩
  exact PE.functional hm2 (hg (v a)) (hm1 ⟨a, rfl⟩)

end Chain

/-- **Existence of monster models.** Every nonempty structure in a language
in `Type` has, for every regular cardinal `κ`, a `κ`-saturated, strongly
`κ`-homogeneous elementary extension (ZFC; no set-theoretic hypothesis). -/
theorem exists_saturated_homogeneous_extension (M : Type) [L.Structure M] [Nonempty M]
    (κ : Cardinal.{0}) (hκ : κ.IsRegular) :
    ∃ (N : Type) (_ : L.Structure N) (_ : M ↪ₑ[L] N), IsSat (L := L) N κ ∧ IsSH (L := L) N κ := by
  have : Fact κ.IsRegular := ⟨hκ⟩
  exact ⟨Mon (L := L) κ M, inferInstance, baseE κ M, mon_sat κ M, mon_sh κ M⟩

end DiamondIntegral.Section5.MonsterModels

namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language HahnSeries
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
local instance monsterSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance monsterSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

theorem rvOfField_zero : rvOfField 0 = none := by
  simp [rvOfField, RVCalc.rv_zero, rvNormalEquiv, _root_.Equiv.optionCongr]

theorem rvOfField_baseUnit (u : (puiseuxBaseSubfield ℂ)ˣ) :
    rvOfField ((u : puiseuxBaseSubfield ℂ) : PuiseuxSeries ℂ) =
      some (puiseuxRVUnitEquiv (puiseuxBaseRVMap u)) := by
  have hf : ((u : puiseuxBaseSubfield ℂ) : PuiseuxSeries ℂ) ≠ 0 :=
    fun h => u.ne_zero (Subtype.ext h)
  rw [rvOfField, RVCalc.rv_of_ne hf]
  have hu : Units.map (puiseuxBaseSubfield ℂ).subtype.toMonoidHom u = Units.mk0 _ hf := Units.ext rfl
  change some (puiseuxRVUnitEquiv (QuotientGroup.mk' _ (Units.mk0 _ hf))) = _
  rw [puiseuxBaseRVMap, MonoidHom.comp_apply, hu]

/-- The RV elements of the Laurent base are exactly the RV images of
Laurent series. -/
theorem baseCarrier_rv_iff (r : RV) :
    baseCarrier (Sum.inr r : Carrier) ↔ ∃ f ∈ puiseuxBaseSubfield ℂ, rvOfField f = r := by
  constructor
  · intro hr
    cases r with
    | none => exact ⟨0, (puiseuxBaseSubfield ℂ).zero_mem, rvOfField_zero⟩
    | some u =>
      obtain ⟨z, hz⟩ := hr
      obtain ⟨w, hw⟩ := puiseuxBaseRVMap_integer (k := ℂ) z u.2
      refine ⟨((w : puiseuxBaseSubfield ℂ) : PuiseuxSeries ℂ), (w : puiseuxBaseSubfield ℂ).2, ?_⟩
      rw [rvOfField_baseUnit, hw]
      exact congrArg some (Prod.ext hz.symm rfl)
  · rintro ⟨f, hf, rfl⟩
    by_cases h0 : f = 0
    · subst h0
      rw [rvOfField_zero]
      trivial
    · let b : puiseuxBaseSubfield ℂ := ⟨f, hf⟩
      have hb : b ≠ 0 := fun h => h0 (congrArg Subtype.val h)
      obtain ⟨z, c, hzc⟩ := puiseuxBaseRVMap_coordinates (k := ℂ) (Units.mk0 b hb)
      have he := rvOfField_baseUnit (Units.mk0 b hb)
      change rvOfField f = _ at he
      rw [he, hzc]
      exact ⟨z, rfl⟩

section Ambient
variable {N : Type} [LRV.Structure N]

/-- Elementary extensions of the concrete model are canonical ACVF models. -/
theorem elementaryAmbient_canonicalACVF (e : Carrier ↪ₑ[LRV] N) :
    N ⊨ Axioms.ACVF ∧ CanonicalStructure.IsCanonical (M := N) :=
  CanonicalTheory.model_CanonicalACVF_iff.mp ((e.theory_model_iff _).mp
    (CanonicalTheory.model_CanonicalACVF_iff.mpr ⟨canonical_model_ACVF, canonicalInterpret_isCanonical⟩))

theorem elementaryAmbient_ACVF00 (e : Carrier ↪ₑ[LRV] N) : N ⊨ Axioms.ACVF00 :=
  (e.theory_model_iff _).mp canonical_model_ACVF00

variable [N ⊨ Axioms.ACVF] (e : Carrier ↪ₑ[LRV] N)

/-- The Laurent field `C((t))` inside the ambient VF sort. -/
def ambientLaurentSubfield : Subfield (VFType (M := N)) :=
  (puiseuxBaseSubfield ℂ).map (ambientPuiseuxFieldHom e)

theorem ambientPuiseux_rv_val (f : PuiseuxSeries ℂ) :
    (CanonicalRV.encodedRv (ambientPuiseuxFieldHom e f)).val = e (Sum.inr (rvOfField f)) := by
  have h := elementaryVFFieldHom_rv e (taggedFieldEquiv.symm f)
  rw [show ambientPuiseuxFieldHom e f = elementaryVFFieldHom e (taggedFieldEquiv.symm f) from rfl, ← h]
  change e (CanonicalRV.encodedRv (taggedFieldEquiv.symm f)).val = _
  congr 1
  change (if ∀ i : Fin 1, @sortEval Carrier interpret .vf
      ((![Sum.inl f] : Fin 1 → Carrier) i) then Sum.inr (rvOfField f) else _) = _
  exact ite_eq_left (by intro i; fin_cases i; trivial)

theorem ambientLaurent_carrier (hc : CanonicalStructure.IsCanonical (M := N)) :
    (vfFieldSubstructure hc (ambientLaurentSubfield e) : Set N) =
      Set.range (e ∘ laurentCoefficientEnumeration) := by
  ext x
  change x ∈ vfFieldCarrier (ambientLaurentSubfield e) ↔ _
  constructor
  · rintro (hx | hx)
    · obtain ⟨b, hb, rfl⟩ := hx
      have hb' : (b : VFType (M := N)) ∈ ambientLaurentSubfield e := hb
      obtain ⟨f, hf, hfb⟩ := (Subfield.mem_map (f := ambientPuiseuxFieldHom e)).mp hb'
      rw [← hfb]
      exact ⟨⟨Sum.inl f, hf⟩, rfl⟩
    · obtain ⟨r, ⟨b, hb, hbr⟩, rfl⟩ := hx
      have hb' : (b : VFType (M := N)) ∈ ambientLaurentSubfield e := hb
      obtain ⟨f, hf, hfb⟩ := (Subfield.mem_map (f := ambientPuiseuxFieldHom e)).mp hb'
      rw [← hbr, ← hfb]
      refine ⟨⟨Sum.inr (rvOfField f), (baseCarrier_rv_iff _).mpr ⟨f, hf, rfl⟩⟩, ?_⟩
      exact (ambientPuiseux_rv_val e f).symm
  · rintro ⟨⟨c, hc'⟩, rfl⟩
    cases c with
    | inl f =>
      exact Or.inl ⟨ambientPuiseuxFieldHom e f, (Subfield.mem_map (f := ambientPuiseuxFieldHom e)).mpr ⟨f, hc', rfl⟩, rfl⟩
    | inr r =>
      obtain ⟨f, hf, rfl⟩ := (baseCarrier_rv_iff r).mp hc'
      refine Or.inr ⟨CanonicalRV.encodedRv (ambientPuiseuxFieldHom e f),
        ⟨ambientPuiseuxFieldHom e f, (Subfield.mem_map (f := ambientPuiseuxFieldHom e)).mpr ⟨f, hf, rfl⟩, rfl⟩, ?_⟩
      exact ambientPuiseux_rv_val e f

theorem ambientLaurent_names (hc : CanonicalStructure.IsCanonical (M := N)) :
    ∀ γ ∈ vfFieldGamma (ambientLaurentSubfield e),
      GammaDefinableClosureAtBase
        (EmptyGammaGround.base (vfFieldSubstructure hc (ambientLaurentSubfield e) : Set N)) γ :=
  vfFieldGamma_names _ _ (fun x hx =>
    definableClosureAt_of_mem ((vfFieldCarrier_vf _ x).mpr hx) x.property)

theorem ambientLaurent_nontrivial :
    ∃ x : (ambientLaurentSubfield e)ˣ, vfFieldGammaMap (ambientLaurentSubfield e) x ≠ 1 := by
  let t : PuiseuxSeries ℂ := (puiseuxBaseUniformizer (k := ℂ)).val
  have ht0 : t ≠ 0 := puiseuxRoot_ne_zero 1
  let a : VFType (M := Carrier) := taggedFieldEquiv.symm t
  let b : VFType (M := N) := ambientPuiseuxFieldHom e t
  have hb0 : b ≠ 0 := (map_ne_zero (ambientPuiseuxFieldHom e)).mpr ht0
  have hbF : b ∈ ambientLaurentSubfield e :=
    (Subfield.mem_map (f := ambientPuiseuxFieldHom e)).mpr ⟨t, (puiseuxBaseUniformizer (k := ℂ)).property, rfl⟩
  let x : ambientLaurentSubfield e := ⟨b, hbF⟩
  have hx0 : x ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
  refine ⟨Units.mk0 x hx0, ?_⟩
  intro he
  have hv : Values.vrv (CanonicalRV.encodedRv b) = (1 : Values.Gamma (M := N)).val :=
    congrArg Subtype.val he
  have hv1 : Values.vrv (CanonicalRV.encodedRv b) =
      Values.vrv (CanonicalRV.encodedRv (1 : VFType (M := N))) :=
    hv.trans Values.vf_value_one.symm
  have hvM : Values.vrv (CanonicalRV.encodedRv a) =
      Values.vrv (CanonicalRV.encodedRv (1 : VFType (M := Carrier))) := by
    apply elementaryGammaTopMap_injective e
    change Values.vrv (elementaryRVMap e (CanonicalRV.encodedRv a)) =
      Values.vrv (elementaryRVMap e (CanonicalRV.encodedRv 1))
    rw [elementaryVFFieldHom_rv, elementaryVFFieldHom_rv, (elementaryVFFieldHom e).map_one]
    exact hv1
  have hval : puiseuxValuation ℂ t = 1 := by
    have heq := ((Values.vrv_eq_iff _ _).mp hvM)
    have h₁ : VFValued.predV a 1 := heq.2
    have h₂ : VFValued.predV 1 a := heq.1
    have h₁' := (taggedFieldEquiv_valuation a 1).mp h₁
    have h₂' := (taggedFieldEquiv_valuation 1 a).mp h₂
    simpa only [a, map_one, RingEquiv.apply_symm_apply] using le_antisymm h₁' h₂'
  have horder := congrArg (fun z : Multiplicative (WithTop ℚ)ᵒᵈ => OrderDual.ofDual z.toAdd) hval
  change (t : HahnSeries ℚ ℂ).orderTop = (0 : WithTop ℚ) at horder
  have htcoe : (t : HahnSeries ℚ ℂ) = single (1 : ℚ) 1 := by
    change (puiseuxRoot (k := ℂ) 1 : HahnSeries ℚ ℂ) = single (1 : ℚ) 1
    norm_num [puiseuxRoot_coe]
  rw [htcoe] at horder
  norm_num [orderTop_single] at horder

theorem ambientLaurent_small {κ : Cardinal} (hsmall : Cardinal.mk Carrier < κ) :
    Cardinal.mk (ambientLaurentSubfield e) < κ := by
  have h₁ : Cardinal.mk (ambientLaurentSubfield e) ≤ Cardinal.mk (PuiseuxSeries ℂ) := by
    change Cardinal.mk ((ambientPuiseuxFieldHom e) '' (puiseuxBaseSubfield ℂ : Set (PuiseuxSeries ℂ))) ≤ _
    exact Cardinal.mk_image_le.trans (Cardinal.mk_set_le _)
  have h₂ : Cardinal.mk (PuiseuxSeries ℂ) ≤ Cardinal.mk Carrier :=
    Cardinal.mk_le_of_injective Sum.inl_injective
  exact (h₁.trans h₂).trans_lt hsmall

/-- The ambient ground context: the actual Laurent field `C((t))` with its
RV image, and its value group, in a saturated strongly homogeneous ambient. -/
def puiseuxAmbientContext (hc : CanonicalStructure.IsCanonical (M := N)) (κ : Cardinal)
    (hκ : Cardinal.aleph0 < κ) (hsmall : Cardinal.mk Carrier < κ)
    (hsat : Saturated N κ) (hhom : StronglyHomogeneous N κ) : GammaGroundContext N where
  model00 := elementaryAmbient_ACVF00 e
  κ := κ
  uncountable := hκ
  saturated := hsat
  homogeneous := hhom
  real := vfFieldSubstructure hc (ambientLaurentSubfield e)
  fieldBase := vfFieldSubstructureBase hc (ambientLaurentSubfield e)
  gamma := vfFieldGamma (ambientLaurentSubfield e)
  values_mem := vfFieldGamma_values_mem (ambientLaurentSubfield e) hc
  small_real := vfFieldSubstructure_small hc _ hκ.le (ambientLaurent_small e hsmall)
  small_gamma := vfFieldGamma_small _ (ambientLaurent_small e hsmall)
  nontrivial_gamma := by
    obtain ⟨x, hx⟩ := ambientLaurent_nontrivial e
    exact ⟨⟨vfFieldGammaMap _ x, ⟨x, rfl⟩⟩, hx⟩

end Ambient


theorem carrier_infinite : Infinite Carrier :=
  Infinite.of_injective (fun c : ℂ => (Sum.inl (puiseuxConstant (k := ℂ) c) : Carrier))
    (fun _ _ h => (puiseuxConstant (k := ℂ)).injective (Sum.inl_injective h))

/-- The project's saturation and homogeneity are the generic notions for `LRV`. -/
theorem saturated_iff_isSat {N : Type} [LRV.Structure N] (κ : Cardinal) :
    Saturated N κ ↔ MonsterModels.IsSat (L := LRV) N κ := Iff.rfl

theorem stronglyHomogeneous_iff_isSH {N : Type} [LRV.Structure N] (κ : Cardinal) :
    StronglyHomogeneous N κ ↔ MonsterModels.IsSH (L := LRV) N κ := Iff.rfl

/-- A saturated, strongly homogeneous elementary extension of the concrete
Puiseux model, at the regular cardinal `succ #Carrier`. -/
theorem exists_puiseux_monster :
    ∃ (N : Type) (_ : LRV.Structure N) (_ : Carrier ↪ₑ[LRV] N) (κ : Cardinal),
      Cardinal.aleph0 < κ ∧ Cardinal.mk Carrier < κ ∧ Saturated N κ ∧ StronglyHomogeneous N κ := by
  have hinf : Cardinal.aleph0 ≤ Cardinal.mk Carrier := by
    have := carrier_infinite
    exact Cardinal.aleph0_le_mk Carrier
  have hreg : (Order.succ (Cardinal.mk Carrier)).IsRegular := Cardinal.isRegular_succ hinf
  obtain ⟨N, sN, e, hsat, hsh⟩ :=
    MonsterModels.exists_saturated_homogeneous_extension (L := LRV) Carrier _ hreg
  exact ⟨N, sN, e, _, hinf.trans_lt (Order.lt_succ _), Order.lt_succ _, hsat, hsh⟩

/-- **The ambient of Notation 5.15 and Corollary 5.21 exists.** All binders of
`corollary_global_vanishing_discharged` are simultaneously satisfiable. -/
theorem exists_puiseux_ambient :
    ∃ (N : Type) (_ : LRV.Structure N) (_ : N ⊨ Axioms.ACVF) (e : Carrier ↪ₑ[LRV] N)
      (G : GammaGroundContext N) (_ : CanonicalStructure.IsCanonical (M := N)),
      G.base.real = Set.range (e ∘ laurentCoefficientEnumeration) ∧
      ∀ γ ∈ G.base.gamma, GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ := by
  obtain ⟨N, sN, e, κ, hκ, hsmall, hsat, hsh⟩ := exists_puiseux_monster
  obtain ⟨hN, hc⟩ := elementaryAmbient_canonicalACVF e
  exact ⟨N, sN, hN, e, puiseuxAmbientContext e hc κ hκ hsmall hsat hsh, hc,
    ambientLaurent_carrier e hc, ambientLaurent_names e hc⟩

/-- The data Notation 5.15 and Corollary 5.21 are parametrized by. This only
bundles their binders; `puiseuxAmbient_nonempty` proves it is inhabited. -/
structure PuiseuxAmbient where
  N : Type
  [str : LRV.Structure N]
  [model : N ⊨ Axioms.ACVF]
  e : Carrier ↪ₑ[LRV] N
  G : GammaGroundContext N
  hc : CanonicalStructure.IsCanonical (M := N)
  hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration)
  hγ : ∀ γ ∈ G.base.gamma, GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ

attribute [instance] PuiseuxAmbient.str PuiseuxAmbient.model

theorem puiseuxAmbient_nonempty : Nonempty PuiseuxAmbient := by
  obtain ⟨N, sN, hN, e, G, hc, hB, hγ⟩ := exists_puiseux_ambient
  exact ⟨{ N := N, e := e, G := G, hc := hc, hB := hB, hγ := hγ }⟩

/-- A fixed ambient, chosen from the existence theorem. -/
def puiseuxAmbient : PuiseuxAmbient := Classical.choice puiseuxAmbient_nonempty

open AlgebraicGeometry SpecialTransformations.Section4 EquivariantVariety in
/-- Notation 5.15's `Vol` on actual complex varieties, in a given ambient. -/
def puiseuxComplexVarietyVolume (A : PuiseuxAmbient) (X : ComplexVariety) : ModifiedRing :=
  complexVarietyVolume_discharged A.e A.G A.hB A.hc A.hγ X

open AlgebraicGeometry SpecialTransformations.Section4 EquivariantVariety in
/-- Corollary 5.21 in a given ambient; `puiseuxAmbient` provides one. -/
theorem puiseux_corollary_global_vanishing (A : PuiseuxAmbient) {X Y : ComplexVariety}
    (f : X.Morphism Y) (c : AffineVarietyPresentation X.trivialObject)
    (d : AffineVarietyPresentation Y.trivialObject) :
    letI : Algebra ℂ (VFType (M := A.N)) := (ambientComplexFieldHom A.e).toAlgebra
    let Aₒ := varietyNativeObject A.e A.G A.hB A.hc c
    let C := (varietyNativeObject A.e A.G A.hB A.hc d).domain
    let hC := varietyNativeObject_groundLabels A.e A.G A.hB A.hc d
    let F := varietyNativeMorphism A.e A.G A.hB A.hc c d f.trivialMorphism
    let hnt := ambientLaurentField_nontrivial A.e A.G A.hB
    (∀ b : Y.trivialObject.fieldPoint (K := VFType (M := A.N)),
      GroundTaggedIntrinsicFibreVanishes GammaQE.gamma_piecewise_rational_affine hnt A.hγ Aₒ C hC F
        (completedGroundTaggedFieldLiftInputs A.G A.hc hnt
          (varietyNativeObject A.e A.G A.hB A.hc d).vfArity
          (varietyNativeObject A.e A.G A.hB A.hc d).rvArity)
        (varietyNativePointEquiv A.e A.G A.hB A.hc d b)) →
      puiseuxComplexVarietyVolume A X = 0 :=
  corollary_global_vanishing_discharged A.e A.G A.hB A.hc A.hγ f c d

open SpecialTransformations.Section4 in
/-- Notation 5.15's bounded VF volume in a given ambient. -/
def puiseuxBoundedVFVolume (A : PuiseuxAmbient) :
    GammaGroundVFGrothendieckRing A.hc A.G.base →+* EquivariantVariety.ModifiedRing :=
  ambientBoundedVFVolume A.e A.hB A.hγ GammaQE.gamma_piecewise_rational_affine
    (completed18GroundLiftInput A.G A.hc)

end DiamondIntegral.Section5.PuiseuxOriginal
