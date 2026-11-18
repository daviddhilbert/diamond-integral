import «section 5».ElementaryRawGraphBijections
import «section 5».ElementaryDefinableNonempty
import «section 5».ElementaryNativeRVOps
import «section 5».ElementaryValueFibreDescent
import «section 5».NativeRawGraphMaps
import «section 5».RawGraphNativeRealization

/-! Extension of actual definable sets and raw definable graph maps along
an elementary embedding, over the same named parameters. Equality,
emptiness and inclusion of extended sets are detected on the smaller
model; extra parameters from the smaller model may be adjoined. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
section Generic
variable {L : Language} {M N P : Type} [L.Structure M] [L.Structure N]
variable (e : M ↪ₑ[L] N) (c : P → M) {n m : ℕ}

def elementaryActualExtension (S : L.DefinableSet (Set.range c) (Fin n)) :
    L.DefinableSet (Set.range (e ∘ c)) (Fin n) :=
  (elementaryActualDefinableEquiv e c).symm S

theorem elementaryActualExtension_mem (S : L.DefinableSet (Set.range c) (Fin n)) (x : Fin n → M) :
    e ∘ x ∈ (elementaryActualExtension e c S).val ↔ x ∈ S.val := by
  have h := congrArg (fun T : L.DefinableSet (Set.range c) (Fin n) => x ∈ T.val)
    ((elementaryActualDefinableEquiv e c).apply_symm_apply S)
  exact h.to_iff

theorem elementaryActual_eq_of_restrict (S T : L.DefinableSet (Set.range (e ∘ c)) (Fin n))
    (h : ∀ x : Fin n → M, e ∘ x ∈ S.val ↔ e ∘ x ∈ T.val) : S = T := by
  apply (elementaryActualDefinableEquiv e c).injective
  apply Subtype.ext
  ext x
  exact h x

theorem elementaryActualExtension_eq_iff (S : L.DefinableSet (Set.range c) (Fin n))
    (T : L.DefinableSet (Set.range (e ∘ c)) (Fin n))
    (h : ∀ x : Fin n → M, e ∘ x ∈ T.val ↔ x ∈ S.val) : elementaryActualExtension e c S = T :=
  elementaryActual_eq_of_restrict e c _ _
    (fun x => (elementaryActualExtension_mem e c S x).trans (h x).symm)

theorem elementaryActual_eq_empty (S : L.DefinableSet (Set.range (e ∘ c)) (Fin n))
    (h : ∀ x : Fin n → M, e ∘ x ∉ S.val) : S.val = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty,elementary_actual_nonempty e c S]
  rintro ⟨x,hx⟩
  exact h x hx

theorem elementaryActual_subset (S T : L.DefinableSet (Set.range (e ∘ c)) (Fin n))
    (h : ∀ x : Fin n → M, e ∘ x ∈ S.val → e ∘ x ∈ T.val) : S.val ⊆ T.val := by
  have he := elementaryActual_eq_empty e c (S \ T) (fun x hx => hx.2 (h x hx.1))
  intro y hy
  by_contra hn
  have hm : y ∈ (S \ T).val := ⟨hy,hn⟩
  rw [he] at hm
  exact hm

theorem elementary_range_mono {P' : Type} (c' : P' → M) (hc : Set.range c ⊆ Set.range c') :
    Set.range (e ∘ c) ⊆ Set.range (e ∘ c') := by
  rintro _ ⟨p,rfl⟩
  obtain ⟨q,hq⟩ := hc ⟨p,rfl⟩
  exact ⟨q,congrArg e hq⟩

/-- Extension is detected on the smaller model even against sets that use
additional parameters from the smaller model. -/
theorem elementaryActualExtension_eq_of_params {P' : Type} (c' : P' → M)
    (hc : Set.range c ⊆ Set.range c') (S : L.DefinableSet (Set.range c) (Fin n))
    (T : Set (Fin n → N)) (hT : (Set.range (e ∘ c')).Definable L T)
    (h : ∀ x : Fin n → M, e ∘ x ∈ T ↔ x ∈ S.val) :
    (elementaryActualExtension e c S).val = T := by
  have he := elementaryActual_eq_of_restrict e c'
    ⟨_,(elementaryActualExtension e c S).property.mono (elementary_range_mono e c c' hc)⟩ ⟨T,hT⟩
    (fun x => (elementaryActualExtension_mem e c S x).trans (h x).symm)
  exact congrArg Subtype.val he

theorem elementaryActualExtension_subset_of_params {P' : Type} (c' : P' → M)
    (hc : Set.range c ⊆ Set.range c') (S : L.DefinableSet (Set.range c) (Fin n))
    (T : Set (Fin n → N)) (hT : (Set.range (e ∘ c')).Definable L T)
    (h : ∀ x : Fin n → M, x ∈ S.val → e ∘ x ∈ T) :
    (elementaryActualExtension e c S).val ⊆ T :=
  elementaryActual_subset e c'
    ⟨_,(elementaryActualExtension e c S).property.mono (elementary_range_mono e c c' hc)⟩ ⟨T,hT⟩
    (fun x hx => h x ((elementaryActualExtension_mem e c S x).mp hx))

theorem elementaryActualExtension_subset (S T : L.DefinableSet (Set.range c) (Fin n))
    (h : S.val ⊆ T.val) :
    (elementaryActualExtension e c S).val ⊆ (elementaryActualExtension e c T).val :=
  elementaryActual_subset e c _ _ (fun x hx =>
    (elementaryActualExtension_mem e c T x).mpr (h ((elementaryActualExtension_mem e c S x).mp hx)))

/-! ## Projections, totality and functionality -/

theorem tuple_append_split {Q : Type} (w : Fin (n+m) → Q) :
    Fin.append (w ∘ Fin.castAdd m) (w ∘ Fin.natAdd n) = w :=
  Fin.append_castAdd_natAdd

theorem tuple_append_left {Q : Type} (x : Fin n → Q) (y : Fin m → Q) :
    Fin.append x y ∘ Fin.castAdd m = x := by
  funext i
  simp

theorem tuple_append_right {Q : Type} (x : Fin n → Q) (y : Fin m → Q) :
    Fin.append x y ∘ Fin.natAdd n = y := by
  funext i
  simp

section Projection
variable {X : Set N}

def definableTupleProjection (G : L.DefinableSet X (Fin (n+m))) : L.DefinableSet X (Fin n) :=
  ⟨(fun w : Fin (n+m) → N => w ∘ Fin.castAdd m) '' G.val,G.property.image_comp _⟩

theorem mem_definableTupleProjection (G : L.DefinableSet X (Fin (n+m))) (x : Fin n → N) :
    x ∈ (definableTupleProjection G).val ↔ ∃ y : Fin m → N,Fin.append x y ∈ G.val := by
  constructor
  · rintro ⟨w,hw,rfl⟩
    refine ⟨w ∘ Fin.natAdd n,?_⟩
    change Fin.append (w ∘ Fin.castAdd m) (w ∘ Fin.natAdd n) ∈ G.val
    rw [tuple_append_split]
    exact hw
  · rintro ⟨y,hy⟩
    exact ⟨Fin.append x y,hy,tuple_append_left x y⟩

def definableTupleSwap (G : L.DefinableSet X (Fin (n+m))) : L.DefinableSet X (Fin (m+n)) :=
  ⟨{w | w ∘ rawTupleSwap n m ∈ G.val},G.property.preimage_comp _⟩

theorem mem_definableTupleSwap (G : L.DefinableSet X (Fin (n+m))) (x : Fin n → N) (y : Fin m → N) :
    Fin.append y x ∈ (definableTupleSwap G).val ↔ Fin.append x y ∈ G.val := by
  change Fin.append y x ∘ rawTupleSwap n m ∈ G.val ↔ _
  rw [rawTupleSwap_append]

theorem definable_tuple_diagonal (i j : Fin n) : X.Definable L {w : Fin n → N | w i = w j} := by
  have h := (Set.Definable.diagonal L X).preimage_comp (![i,j] : Fin 2 → Fin n)
  convert h using 1
  ext w
  simp [Set.mem_diagonal_iff]

theorem definable_tuple_ne {k : ℕ} (σ τ : Fin k → Fin n) :
    X.Definable L {w : Fin n → N | w ∘ σ ≠ w ∘ τ} := by
  have h : X.Definable L (⋃ j : Fin k,{w : Fin n → N | w (σ j) = w (τ j)}ᶜ) :=
    Set.definable_iUnion_of_finite (fun j => (definable_tuple_diagonal (σ j) (τ j)).compl)
  convert h using 1
  ext w
  simp only [ne_eq,Set.mem_iUnion,Set.mem_compl_iff]
  constructor
  · intro hw
    by_contra hn
    exact hw (funext (fun j => by_contra (fun hj => hn ⟨j,hj⟩)))
  · rintro ⟨j,hj⟩ he
    exact hj (congrFun he j)

end Projection

theorem elementary_total_transfer (A : L.DefinableSet (Set.range (e ∘ c)) (Fin n))
    (G : L.DefinableSet (Set.range (e ∘ c)) (Fin (n+m)))
    (h : ∀ x : Fin n → M,e ∘ x ∈ A.val → ∃ y : Fin m → M,e ∘ Fin.append x y ∈ G.val) :
    ∀ x ∈ A.val,∃ y : Fin m → N,Fin.append x y ∈ G.val := by
  have hs := elementaryActual_subset e c A (definableTupleProjection G) (by
    intro x hx
    obtain ⟨y,hy⟩ := h x hx
    rw [mem_definableTupleProjection]
    exact ⟨e ∘ y,by rwa [raw_tuple_comp_append] at hy⟩)
  intro x hx
  exact (mem_definableTupleProjection G x).mp (hs hx)

def tripleSecondIndex (n m : ℕ) : Fin (n+m) → Fin ((n+m)+m) :=
  Fin.append (Fin.castAdd m ∘ Fin.castAdd m) (Fin.natAdd (n+m))

theorem tripleSecondIndex_append {Q : Type} (x : Fin n → Q) (y z : Fin m → Q) :
    Fin.append (Fin.append x y) z ∘ tripleSecondIndex n m = Fin.append x z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [tripleSecondIndex,Function.comp_def]

theorem triple_first_append {Q : Type} (x : Fin n → Q) (y z : Fin m → Q) :
    Fin.append (Fin.append x y) z ∘ Fin.castAdd m = Fin.append x y := by
  funext i
  simp

theorem triple_middle {Q : Type} (x : Fin n → Q) (y z : Fin m → Q) :
    Fin.append (Fin.append x y) z ∘ (Fin.castAdd m ∘ Fin.natAdd n) = y := by
  funext i
  simp

theorem triple_last {Q : Type} (x : Fin n → Q) (y z : Fin m → Q) :
    Fin.append (Fin.append x y) z ∘ Fin.natAdd (n+m) = z := by
  funext i
  simp

theorem elementary_functional_transfer (G : L.DefinableSet (Set.range (e ∘ c)) (Fin (n+m)))
    (h : ∀ (x : Fin n → M) (y z : Fin m → M),e ∘ Fin.append x y ∈ G.val →
      e ∘ Fin.append x z ∈ G.val → y = z) :
    ∀ (x : Fin n → N) (y z : Fin m → N),Fin.append x y ∈ G.val → Fin.append x z ∈ G.val → y = z := by
  let U : L.DefinableSet (Set.range (e ∘ c)) (Fin ((n+m)+m)) :=
    ⟨{w | w ∘ Fin.castAdd m ∈ G.val} ∩ {w | w ∘ tripleSecondIndex n m ∈ G.val} ∩
      {w | w ∘ (Fin.castAdd m ∘ Fin.natAdd n) ≠ w ∘ Fin.natAdd (n+m)},
      ((G.property.preimage_comp _).inter (G.property.preimage_comp _)).inter (definable_tuple_ne _ _)⟩
  have hU := elementaryActual_eq_empty e c U (by
    rintro v ⟨⟨h1,h2⟩,h3⟩
    have hvv : v = Fin.append (Fin.append ((v ∘ Fin.castAdd m) ∘ Fin.castAdd m)
        ((v ∘ Fin.castAdd m) ∘ Fin.natAdd n)) (v ∘ Fin.natAdd (n+m)) := by
      rw [tuple_append_split,tuple_append_split]
    generalize (v ∘ Fin.castAdd m) ∘ Fin.castAdd m = x at hvv
    generalize (v ∘ Fin.castAdd m) ∘ Fin.natAdd n = y at hvv
    generalize v ∘ Fin.natAdd (n+m) = z at hvv
    subst hvv
    change (e ∘ Fin.append (Fin.append x y) z) ∘ Fin.castAdd m ∈ G.val at h1
    change (e ∘ Fin.append (Fin.append x y) z) ∘ tripleSecondIndex n m ∈ G.val at h2
    change (e ∘ Fin.append (Fin.append x y) z) ∘ (Fin.castAdd m ∘ Fin.natAdd n) ≠
      (e ∘ Fin.append (Fin.append x y) z) ∘ Fin.natAdd (n+m) at h3
    rw [Function.comp_assoc,triple_first_append] at h1
    rw [Function.comp_assoc,tripleSecondIndex_append] at h2
    rw [Function.comp_assoc,Function.comp_assoc,triple_middle,triple_last] at h3
    exact h3 (congrArg (fun t => e ∘ t) (h x y z h1 h2)))
  intro x y z hy hz
  by_contra hne
  have hm : Fin.append (Fin.append x y) z ∈ U.val := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · change Fin.append (Fin.append x y) z ∘ Fin.castAdd m ∈ G.val
      rw [triple_first_append]
      exact hy
    · change Fin.append (Fin.append x y) z ∘ tripleSecondIndex n m ∈ G.val
      rw [tripleSecondIndex_append]
      exact hz
    · change Fin.append (Fin.append x y) z ∘ (Fin.castAdd m ∘ Fin.natAdd n) ≠
        Fin.append (Fin.append x y) z ∘ Fin.natAdd (n+m)
      rw [triple_middle,triple_last]
      exact hne
  rw [hU] at hm
  exact hm

/-! ## Extension of raw definable graph maps -/

variable {A : L.DefinableSet (Set.range c) (Fin n)} {B : L.DefinableSet (Set.range c) (Fin m)}

namespace RawDefinableGraphMap

theorem graph_functional (f : RawDefinableGraphMap c A B) (x : Fin n → M) (y z : Fin m → M)
    (hy : Fin.append x y ∈ f.graph.val) (hz : Fin.append x z ∈ f.graph.val) : y = z := by
  obtain ⟨a,ha,rfl⟩ := (f.graph_append_iff x y).mp hy
  obtain ⟨b,hb,rfl⟩ := (f.graph_append_iff x z).mp hz
  have hab : a = b := Subtype.ext (ha.trans hb.symm)
  rw [hab]

def extensionGraph (f : RawDefinableGraphMap c A B) :
    L.DefinableSet (Set.range (e ∘ c)) (Fin (n+m)) :=
  elementaryActualExtension e c f.graph

theorem extension_total (f : RawDefinableGraphMap c A B) :
    ∀ x ∈ (elementaryActualExtension e c A).val,∃ y : Fin m → N,
      Fin.append x y ∈ (f.extensionGraph e c).val := by
  apply elementary_total_transfer
  intro x hx
  have ha := (elementaryActualExtension_mem e c A x).mp hx
  refine ⟨(f.toFun ⟨x,ha⟩).val,?_⟩
  exact (elementaryActualExtension_mem e c f.graph _).mpr ⟨⟨x,ha⟩,rfl⟩

theorem extension_functional (f : RawDefinableGraphMap c A B) (x : Fin n → N) (y z : Fin m → N)
    (hy : Fin.append x y ∈ (f.extensionGraph e c).val)
    (hz : Fin.append x z ∈ (f.extensionGraph e c).val) : y = z := by
  apply elementary_functional_transfer e c (f.extensionGraph e c) _ x y z hy hz
  intro x y z hy hz
  exact f.graph_functional c x y z ((elementaryActualExtension_mem e c f.graph _).mp hy)
    ((elementaryActualExtension_mem e c f.graph _).mp hz)

theorem extension_source_target (f : RawDefinableGraphMap c A B) (x : Fin n → N) (y : Fin m → N)
    (h : Fin.append x y ∈ (f.extensionGraph e c).val) :
    x ∈ (elementaryActualExtension e c A).val ∧ y ∈ (elementaryActualExtension e c B).val := by
  let T : L.DefinableSet (Set.range (e ∘ c)) (Fin (n+m)) :=
    ⟨{w | w ∘ Fin.castAdd m ∈ (elementaryActualExtension e c A).val} ∩
      {w | w ∘ Fin.natAdd n ∈ (elementaryActualExtension e c B).val},
      ((elementaryActualExtension e c A).property.preimage_comp _).inter
        ((elementaryActualExtension e c B).property.preimage_comp _)⟩
  have hs := elementaryActual_subset e c (f.extensionGraph e c) T (by
    intro w hw
    have hg := (elementaryActualExtension_mem e c f.graph w).mp hw
    rw [← tuple_append_split w] at hg
    obtain ⟨a,ha,hb⟩ := (f.graph_append_iff _ _).mp hg
    constructor
    · change e ∘ (w ∘ Fin.castAdd m) ∈ (elementaryActualExtension e c A).val
      rw [elementaryActualExtension_mem,← ha]
      exact a.property
    · change e ∘ (w ∘ Fin.natAdd n) ∈ (elementaryActualExtension e c B).val
      rw [elementaryActualExtension_mem,← hb]
      exact (f.toFun a).property)
  obtain ⟨h1,h2⟩ := hs h
  have h1' : Fin.append x y ∘ Fin.castAdd m ∈ (elementaryActualExtension e c A).val := h1
  have h2' : Fin.append x y ∘ Fin.natAdd n ∈ (elementaryActualExtension e c B).val := h2
  rw [tuple_append_left] at h1'
  rw [tuple_append_right] at h2'
  exact ⟨h1',h2'⟩

def extensionFun (f : RawDefinableGraphMap c A B) :
    (elementaryActualExtension e c A).val → (elementaryActualExtension e c B).val :=
  fun x => ⟨Classical.choose (f.extension_total e c x.val x.property),
    (f.extension_source_target e c _ _ (Classical.choose_spec (f.extension_total e c x.val x.property))).2⟩

theorem extensionFun_graph (f : RawDefinableGraphMap c A B) (x : (elementaryActualExtension e c A).val) :
    Fin.append x.val (f.extensionFun e c x).val ∈ (f.extensionGraph e c).val :=
  Classical.choose_spec (f.extension_total e c x.val x.property)

theorem extensionFun_eq_iff (f : RawDefinableGraphMap c A B) (x : (elementaryActualExtension e c A).val)
    (y : Fin m → N) :
    (f.extensionFun e c x).val = y ↔ Fin.append x.val y ∈ (f.extensionGraph e c).val := by
  constructor
  · rintro rfl
    exact f.extensionFun_graph e c x
  · intro h
    exact f.extension_functional e c x.val _ _ (f.extensionFun_graph e c x) h

theorem extensionFun_graph_eq (f : RawDefinableGraphMap c A B) :
    {w | ∃ a : (elementaryActualExtension e c A).val,w = Fin.append a.val (f.extensionFun e c a).val} =
      (f.extensionGraph e c).val := by
  ext w
  constructor
  · rintro ⟨a,rfl⟩
    exact f.extensionFun_graph e c a
  · intro hw
    rw [← tuple_append_split w] at hw ⊢
    have hs := f.extension_source_target e c _ _ hw
    refine ⟨⟨w ∘ Fin.castAdd m,hs.1⟩,?_⟩
    rw [(f.extensionFun_eq_iff e c ⟨w ∘ Fin.castAdd m,hs.1⟩ (w ∘ Fin.natAdd n)).mpr hw]

def extension (f : RawDefinableGraphMap c A B) :
    RawDefinableGraphMap (e ∘ c) (elementaryActualExtension e c A) (elementaryActualExtension e c B) where
  toFun := f.extensionFun e c
  graph_definable := (f.extensionFun_graph_eq e c).symm ▸ (f.extensionGraph e c).property

theorem extension_apply (f : RawDefinableGraphMap c A B) (x : (elementaryActualExtension e c A).val) :
    ((f.extension e c).toFun x).val = (f.extensionFun e c x).val := rfl

theorem extension_bijective (f : RawDefinableGraphMap c A B) (hf : Function.Bijective f.toFun) :
    Function.Bijective (f.extension e c).toFun := by
  constructor
  · intro x₁ x₂ he
    have h₁ := f.extensionFun_graph e c x₁
    have h₂ := f.extensionFun_graph e c x₂
    have he' : (f.extensionFun e c x₁).val = (f.extensionFun e c x₂).val := congrArg Subtype.val he
    rw [he'] at h₁
    rw [← mem_definableTupleSwap] at h₁ h₂
    apply Subtype.ext
    apply elementary_functional_transfer e c (definableTupleSwap (f.extensionGraph e c)) _ _ _ _ h₁ h₂
    intro y x z hx hz
    change e ∘ Fin.append y x ∈ (definableTupleSwap (f.extensionGraph e c)).val at hx
    change e ∘ Fin.append y z ∈ (definableTupleSwap (f.extensionGraph e c)).val at hz
    rw [raw_tuple_comp_append,mem_definableTupleSwap,← raw_tuple_comp_append] at hx hz
    obtain ⟨a,ha,hay⟩ := (f.graph_append_iff x y).mp ((elementaryActualExtension_mem e c f.graph _).mp hx)
    obtain ⟨b,hb,hby⟩ := (f.graph_append_iff z y).mp ((elementaryActualExtension_mem e c f.graph _).mp hz)
    have hab : a = b := hf.1 (Subtype.ext (hay.trans hby.symm))
    rw [← ha,← hb,hab]
  · intro y
    obtain ⟨x,hx⟩ := elementary_total_transfer e c (elementaryActualExtension e c B)
      (definableTupleSwap (f.extensionGraph e c)) (by
        intro y hy
        obtain ⟨a,ha⟩ := hf.2 ⟨y,(elementaryActualExtension_mem e c B y).mp hy⟩
        refine ⟨a.val,?_⟩
        rw [raw_tuple_comp_append,mem_definableTupleSwap,← raw_tuple_comp_append]
        exact (elementaryActualExtension_mem e c f.graph _).mpr ⟨a,by rw [ha]⟩) y.val y.property
    rw [mem_definableTupleSwap] at hx
    have hs := f.extension_source_target e c _ _ hx
    refine ⟨⟨x,hs.1⟩,Subtype.ext ?_⟩
    exact (f.extensionFun_eq_iff e c ⟨x,hs.1⟩ y.val).mpr hx

end RawDefinableGraphMap

end Generic

/-! ## Native RV domains over the image parameters -/

section Native
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M N P : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
variable (hcM : CanonicalStructure.IsCanonical (M := M)) (hcN : CanonicalStructure.IsCanonical (M := N))
variable (e : M ↪ₑ[LRV] N) (c : P → M) {n m : ℕ}
local notation "Bₙ" => EmptyGammaGround.base (Set.range (e ∘ c))
local notation "Bₘ" => EmptyGammaGround.base (Set.range c)

omit [N ⊨ Axioms.ACVF] in
theorem definable_rv_coordinate (X : Set N) (i : Fin n) :
    X.Definable LRV {x : Fin n → N | iRV (x i)} := by
  rw [Set.definable_iff_exists_formula_sum]
  refine ⟨Relations.formula₁ (L := LRV) Rel.memRV (Term.var (Sum.inr i)),?_⟩
  ext x
  simp only [Set.mem_ofPred_eq,Formula.realize_rel₁,Term.realize_var,Sum.elim_inr]
  rfl

omit [N ⊨ Axioms.ACVF] in
theorem definable_rv_tuples (X : Set N) : X.Definable LRV {x : Fin n → N | ∀ i,iRV (x i)} := by
  have h := Set.definable_iInter_of_finite (fun i : Fin n => definable_rv_coordinate X i)
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_iInter]

omit [N ⊨ Axioms.ACVF] in
theorem definable_rvLe_left (X : Set N) (i : Fin n) (a : N) (ha : a ∈ X) :
    X.Definable LRV {x : Fin n → N | iLe (x i) a} := by
  rw [Set.definable_iff_exists_formula_sum]
  refine ⟨Relations.formula₂ (L := LRV) Rel.rvLe (Term.var (Sum.inr i)) (Term.var (Sum.inl ⟨a,ha⟩)),?_⟩
  ext x
  simp only [Set.mem_ofPred_eq,Formula.realize_rel₂,Term.realize_var,Sum.elim_inr,Sum.elim_inl]
  rfl

omit [N ⊨ Axioms.ACVF] in
theorem definable_rvLe_right (X : Set N) (i : Fin n) (a : N) (ha : a ∈ X) :
    X.Definable LRV {x : Fin n → N | iLe a (x i)} := by
  rw [Set.definable_iff_exists_formula_sum]
  refine ⟨Relations.formula₂ (L := LRV) Rel.rvLe (Term.var (Sum.inl ⟨a,ha⟩)) (Term.var (Sum.inr i)),?_⟩
  ext x
  simp only [Set.mem_ofPred_eq,Formula.realize_rel₂,Term.realize_var,Sum.elim_inr,Sum.elim_inl]
  rfl

theorem mem_rawDomain_iff {Q : Type} [LRV.Structure Q] [Q ⊨ Axioms.ACVF]
    {hc : CanonicalStructure.IsCanonical (M := Q)} {B : Base (M := Q)}
    (D : GammaGroundDefSet hc B (rawRVSpace (M := Q) n)) (t : Fin n → CanonicalRV.RVSort Q) :
    rvValues t ∈ rawDomain D ↔ t ∈ D.carrier := by
  constructor
  · rintro ⟨u,hu,he⟩
    exact (rvValues_injective he) ▸ hu
  · intro ht
    exact ⟨t,ht,rfl⟩

theorem rawDomain_sorted {Q : Type} [LRV.Structure Q] [Q ⊨ Axioms.ACVF]
    {hc : CanonicalStructure.IsCanonical (M := Q)} {B : Base (M := Q)}
    (D : GammaGroundDefSet hc B (rawRVSpace (M := Q) n)) :
    ∀ x ∈ rawDomain D,∀ i,iRV (x i) := by
  rintro _ ⟨t,_,rfl⟩ i
  exact (t i).property

def elementaryNativeRawExtension (D : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) n)) :
    LRV.DefinableSet (Set.range (e ∘ c)) (Fin n) :=
  elementaryActualExtension e c (nativeRawDomainSet hcM c D)

omit [N ⊨ Axioms.ACVF] in
theorem elementaryNativeRawExtension_mem (D : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) n))
    (x : Fin n → M) : e ∘ x ∈ (elementaryNativeRawExtension hcM e c D).val ↔ x ∈ rawDomain D :=
  elementaryActualExtension_mem e c _ x

theorem elementaryNativeRawExtension_sorted (D : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) n)) :
    ∀ x ∈ (elementaryNativeRawExtension hcM e c D).val,∀ i,iRV (x i) :=
  elementaryActual_subset e c (elementaryNativeRawExtension hcM e c D)
    ⟨{x | ∀ i,iRV (x i)},definable_rv_tuples _⟩ (fun x hx i =>
      (elementaryRVSort_iff e (x i)).mpr
        (rawDomain_sorted D x ((elementaryNativeRawExtension_mem hcM e c D x).mp hx) i))

def elementaryNativeRVExtension (D : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) n)) :
    GammaGroundDefSet hcN Bₙ (rawRVSpace (M := N) n) :=
  rawRVSetNative hcN (e ∘ c) (elementaryNativeRawExtension hcM e c D)
    (elementaryNativeRawExtension_sorted hcM e c D)

theorem elementaryNativeRVExtension_mem (D : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) n))
    (t : Fin n → CanonicalRV.RVSort N) :
    t ∈ (elementaryNativeRVExtension hcM hcN e c D).carrier ↔
      rvValues t ∈ (elementaryNativeRawExtension hcM e c D).val := Iff.rfl

theorem elementaryNativeRVExtension_mem_image (D : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) n))
    (x : Fin n → CanonicalRV.RVSort M) :
    elementaryRVMap e ∘ x ∈ (elementaryNativeRVExtension hcM hcN e c D).carrier ↔ x ∈ D.carrier := by
  rw [elementaryNativeRVExtension_mem]
  exact (elementaryNativeRawExtension_mem hcM e c D (rvValues x)).trans (mem_rawDomain_iff D x)

theorem elementaryNativeRVRestriction_extension (D : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) n)) :
    (elementaryNativeRVRestriction hcM hcN e c (elementaryNativeRVExtension hcM hcN e c D)).carrier =
      D.carrier := by
  ext x
  rw [elementaryNativeRVRestriction_mem,elementaryNativeRVExtension_mem_image]

theorem elementaryNativeRawExtension_restriction (D : GammaGroundDefSet hcN Bₙ (rawRVSpace (M := N) n)) :
    elementaryNativeRawExtension hcM e c (elementaryNativeRVRestriction hcM hcN e c D) =
      nativeRawDomainSet hcN (e ∘ c) D := by
  apply elementaryActualExtension_eq_iff
  intro x
  change e ∘ x ∈ rawDomain D ↔ x ∈ rawDomain (elementaryNativeRVRestriction hcM hcN e c D)
  rw [elementaryNativeRVRestriction,rawDomain_ofRaw]
  rfl

/-- An extension is determined by its restriction. -/
theorem elementaryNativeRVExtension_carrier_eq (D : GammaGroundDefSet hcN Bₙ (rawRVSpace (M := N) n))
    (E : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) n))
    (h : (elementaryNativeRVRestriction hcM hcN e c D).carrier = E.carrier) :
    (elementaryNativeRVExtension hcM hcN e c E).carrier = D.carrier := by
  have hraw : nativeRawDomainSet hcM c E =
      nativeRawDomainSet hcM c (elementaryNativeRVRestriction hcM hcN e c D) := by
    apply Subtype.ext
    change rvValues '' E.carrier = rvValues '' (elementaryNativeRVRestriction hcM hcN e c D).carrier
    rw [h]
  ext t
  change rvValues t ∈ (elementaryActualExtension e c (nativeRawDomainSet hcM c E)).val ↔ t ∈ D.carrier
  rw [hraw]
  change rvValues t ∈ (elementaryNativeRawExtension hcM e c (elementaryNativeRVRestriction hcM hcN e c D)).val ↔ _
  rw [elementaryNativeRawExtension_restriction]
  exact mem_rawDomain_iff D t

theorem elementaryNativeRVExtension_restriction (D : GammaGroundDefSet hcN Bₙ (rawRVSpace (M := N) n)) :
    (elementaryNativeRVExtension hcM hcN e c (elementaryNativeRVRestriction hcM hcN e c D)).carrier =
      D.carrier :=
  elementaryNativeRVExtension_carrier_eq hcM hcN e c D _ rfl

theorem elementaryNativeRVExtension_subset (D E : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) n))
    (h : D.carrier ⊆ E.carrier) :
    (elementaryNativeRVExtension hcM hcN e c D).carrier ⊆ (elementaryNativeRVExtension hcM hcN e c E).carrier := by
  intro t ht
  apply elementaryActualExtension_subset e c (nativeRawDomainSet hcM c D) (nativeRawDomainSet hcM c E) _ ht
  rintro _ ⟨u,hu,rfl⟩
  exact ⟨u,h hu,rfl⟩

theorem elementaryNativeRVExtension_finite (D : GammaGroundDefSet hcM Bₘ (rawRVSpace (M := M) n))
    (hD : GammaRVFiniteValues hcM Bₘ D) :
    GammaRVFiniteValues hcN Bₙ (elementaryNativeRVExtension hcM hcN e c D) := by
  let Pat := (fun t i => Values.vrv (t i)) '' D.carrier
  have hfin : Finite Pat := hD.to_subtype
  let rep : Pat → Fin n → CanonicalRV.RVSort M := fun p => Classical.choose p.property
  have hrep (p : Pat) : rep p ∈ D.carrier ∧ (fun i => Values.vrv (rep p i)) = p.val :=
    Classical.choose_spec p.property
  let c' : P ⊕ (Pat × Fin n) → M := Sum.elim c (fun q => (rep q.1 q.2).val)
  have hcc : Set.range c ⊆ Set.range c' := by
    rintro _ ⟨p,rfl⟩
    exact ⟨Sum.inl p,rfl⟩
  have hmem (q : Pat × Fin n) : e (rep q.1 q.2).val ∈ Set.range (e ∘ c') := ⟨Sum.inr q,rfl⟩
  let Good : Set (Fin n → N) := ⋃ p : Pat,⋂ i : Fin n,
    ({x | iLe (x i) (e (rep p i).val)} ∩ {x | iLe (e (rep p i).val) (x i)})
  have hGood : (Set.range (e ∘ c')).Definable LRV Good :=
    Set.definable_iUnion_of_finite (fun p => Set.definable_iInter_of_finite (fun i =>
      (definable_rvLe_left _ i _ (hmem (p,i))).inter (definable_rvLe_right _ i _ (hmem (p,i)))))
  have hsub := elementaryActualExtension_subset_of_params e c c' hcc (nativeRawDomainSet hcM c D) Good hGood (by
    rintro _ ⟨t,ht,rfl⟩
    let p : Pat := ⟨fun i => Values.vrv (t i),t,ht,rfl⟩
    simp only [Good,Set.mem_iUnion,Set.mem_iInter,Set.mem_inter_iff,Set.mem_ofPred_eq]
    refine ⟨p,fun i => ?_⟩
    have hv : Values.vrv (t i) = Values.vrv (rep p i) := (congrFun (hrep p).2 i).symm
    have hs := (Values.vrv_eq_iff _ _).mp hv
    exact ⟨(elementaryRVMap_le e _ _).mpr hs.1,(elementaryRVMap_le e _ _).mpr hs.2⟩)
  apply (hD.image (fun p => elementaryGammaTopMap e ∘ p)).subset
  rintro _ ⟨t,ht,rfl⟩
  have hg := hsub ht
  simp only [Good,Set.mem_iUnion,Set.mem_iInter,Set.mem_inter_iff,Set.mem_ofPred_eq] at hg
  obtain ⟨p,hp⟩ := hg
  refine ⟨p.val,p.property,?_⟩
  funext i
  have hv : Values.vrv (elementaryRVMap e (rep p i)) = Values.vrv (t i) :=
    (Values.vrv_eq_iff _ _).mpr ⟨(hp i).2,(hp i).1⟩
  change elementaryGammaTopMap e (p.val i) = Values.vrv (t i)
  rw [← congrFun (hrep p).2 i]
  exact hv

include hcN in
theorem elementary_value_fibre_extension (β : Values.Gamma (M := M))
    (hβ : GammaDefinableClosureAtBase Bₘ β) :
    ∃ α : Values.Gamma (M := N),∃ _ : GammaDefinableClosureAtBase Bₙ α,
      elementaryGammaTopMap e β.val = α.val ∧
      (elementaryActualExtension e c ⟨fullRawValueFibre β,
        (fullRawValueFibre_definable_iff hcM _ β).mpr hβ⟩).val = fullRawValueFibre α := by
  obtain ⟨u,hu⟩ := fullRawValueFibre_nonempty β
  obtain ⟨r,_,hrv⟩ := (fullRawValueFibre_mem β u).mp hu
  have hr0 : r.val ≠ iRVZero := fun hz => β.property (hrv.symm.trans ((Values.vrv_eq_infinity_iff r).mpr hz))
  let s := elementaryRVMap e r
  have hs0 : s.val ≠ iRVZero := by
    intro hz
    exact hr0 (e.injective (hz.trans (elementary_iRVZero e).symm))
  let α := Values.gammaOf s hs0
  have hβα : elementaryGammaTopMap e β.val = α.val := (congrArg (elementaryGammaTopMap e) hrv).symm
  let c' : P ⊕ Unit → M := Sum.elim c (fun _ => r.val)
  have hcc : Set.range c ⊆ Set.range c' := by
    rintro _ ⟨p,rfl⟩
    exact ⟨Sum.inl p,rfl⟩
  have hsm : s.val ∈ Set.range (e ∘ c') := ⟨Sum.inr (),rfl⟩
  have hT : fullRawValueFibre α =
      {x : Fin 1 → N | iRV (x 0)} ∩ {x | iLe (x 0) s.val} ∩ {x | iLe s.val (x 0)} := by
    ext x
    rw [fullRawValueFibre_mem]
    constructor
    · rintro ⟨t,ht,hv⟩
      have hst := (Values.vrv_eq_iff t s).mp hv
      have h0 : iRV (x 0) := ht ▸ t.property
      have h1 : iLe (x 0) s.val := ht ▸ hst.1
      have h2 : iLe s.val (x 0) := ht ▸ hst.2
      exact ⟨⟨h0,h1⟩,h2⟩
    · rintro ⟨⟨h0,h1⟩,h2⟩
      exact ⟨⟨x 0,h0⟩,rfl,(Values.vrv_eq_iff ⟨x 0,h0⟩ s).mpr ⟨h1,h2⟩⟩
  have hTd : (Set.range (e ∘ c')).Definable LRV (fullRawValueFibre α) := by
    rw [hT]
    exact ((definable_rv_coordinate _ 0).inter (definable_rvLe_left _ 0 _ hsm)).inter
      (definable_rvLe_right _ 0 _ hsm)
  have hext := elementaryActualExtension_eq_of_params e c c' hcc
    ⟨fullRawValueFibre β,(fullRawValueFibre_definable_iff hcM _ β).mpr hβ⟩ (fullRawValueFibre α) hTd
    (fun x => elementary_full_fibre_preimage e α β hβα x)
  have hα : GammaDefinableClosureAtBase Bₙ α := by
    apply (fullRawValueFibre_definable_iff hcN _ α).mp
    rw [← hext]
    exact (elementaryActualExtension e c _).property
  exact ⟨α,hα,hβα,hext⟩

/-! ## Native maps and bijections -/

variable {D : GammaGroundDefSet hcM (EmptyGammaGround.base (Set.range c)) (rawRVSpace (M := M) n)}
variable {E : GammaGroundDefSet hcM (EmptyGammaGround.base (Set.range c)) (rawRVSpace (M := M) m)}

def elementaryNativeRVExtensionMap (f : GammaGroundMap D E) :
    GammaGroundMap (elementaryNativeRVExtension hcM hcN e c D) (elementaryNativeRVExtension hcM hcN e c E) :=
  rawGraphNativeMap hcN (e ∘ c) (elementaryNativeRawExtension_sorted hcM e c D)
    (elementaryNativeRawExtension_sorted hcM e c E) ((nativeRawGraphMap f).extension e c)

theorem elementaryNativeRVExtensionMap_bijective (f : GammaGroundMap D E) (hf : Function.Bijective f) :
    Function.Bijective (elementaryNativeRVExtensionMap hcM hcN e c f) :=
  rawGraphNativeMap_bijective hcN (e ∘ c) _ _ _
    ((nativeRawGraphMap f).extension_bijective e c (nativeRawGraphMap_bijective f hf))

def elementaryNativeRVExtensionBijection (f : GammaGroundBijection D E) :
    GammaGroundBijection (elementaryNativeRVExtension hcM hcN e c D)
      (elementaryNativeRVExtension hcM hcN e c E) :=
  ⟨elementaryNativeRVExtensionMap hcM hcN e c f.map,
    elementaryNativeRVExtensionMap_bijective hcM hcN e c f.map f.bijective⟩

end Native

end DiamondIntegral.Section5
