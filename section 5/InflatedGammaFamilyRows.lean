import «section 3».GammaTopPresentation
import «section 3».FullGammaTupleAbstraction
import «section 3».GammaGroundFiniteVFObjects
import «section 3».GammaGroundNameReduction
import «section 3».GammaGroundMonotoneBases
import «section 3».GammaGroundFunctionalRelations
import «section 3».GammaGroundMapTuples
import «section 3».GammaGroundRVProductScissors
import «section 4».Section3GammaCodeBridge

/-! Families of finite-RV-fibre VF objects over a Gamma parameter space,
their value-fibre inflation and their rows at Gamma tuples. All sets are
definable over the original base; a row at `γ` is definable over the base
with the names `γ` adjoined, and over the original base when every
coordinate of `γ` is definable there. The value coordinate of the inflation
is `vv x`, expressed through the total valuation into `Γ ∪ {∞}`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- The Gamma parameter space `Γ^n`, presented by all nonzero RV codes. -/
abbrev inflatedGammaPower (hc : CanonicalStructure.IsCanonical (M := M)) (n : ℕ) : Space LRV M :=
  (volumeGammaSpace hc).power (Fin n)

/-! ### Basic definable maps over the real base -/

/-- Coordinate reindexing of RV tuples. -/
def inflatedRVReindexMap (S : Set M) {a b : ℕ} (f : Fin b → Fin a) :
    Map (DefSet.univ (rawRVSpace (M := M) a) S) (DefSet.univ (rawRVSpace (M := M) b) S) := by
  have hdom (c : (rawRVSpace (M := M) a).domain) : c.val ∘ f ∈ (rawRVSpace (M := M) b).domain :=
    ⟨((rawRVSpace a).decode c) ∘ f, by
      funext i
      exact congrFun (rvValues_decode c) (f i)⟩
  refine Map.ofCodes _ (fun x => x ∘ f) (fun z => z ∘ f) (fun _ => Set.DefinableFun.proj LRV) hdom ?_
  intro c
  apply rvValues_injective
  rw [rvValues_decode]
  funext i
  exact (congrFun (rvValues_decode c) (f i)).symm

omit [M ⊨ Axioms.ACVF] in
@[simp] theorem inflatedRVReindexMap_value (S : Set M) {a b : ℕ} (f : Fin b → Fin a)
    (x : DefSet.univ (rawRVSpace (M := M) a) S) :
    (inflatedRVReindexMap S f x).val = x.val ∘ f := rfl

/-- Coordinate reindexing of VF tuples. -/
def inflatedVFReindexMap (S : Set M) {a b : ℕ} (f : Fin b → Fin a) :
    Map (DefSet.univ (rawVFSpace (M := M) a) S) (DefSet.univ (rawVFSpace (M := M) b) S) := by
  have hcode {k : ℕ} (c : (rawVFSpace (M := M) k).domain) : vfValues ((rawVFSpace k).decode c) = c.val :=
    Space.ofEmbedding_decode vfValues vfValues_injective (rawVFSpace (M := M) k).domain_definable c
  have hdom (c : (rawVFSpace (M := M) a).domain) : c.val ∘ f ∈ (rawVFSpace (M := M) b).domain :=
    ⟨((rawVFSpace a).decode c) ∘ f, by
      funext i
      exact congrFun (hcode c) (f i)⟩
  refine Map.ofCodes _ (fun x => x ∘ f) (fun z => z ∘ f) (fun _ => Set.DefinableFun.proj LRV) hdom ?_
  intro c
  apply vfValues_injective
  rw [hcode]
  funext i
  exact (congrFun (hcode c) (f i)).symm

omit [M ⊨ Axioms.ACVF] in
@[simp] theorem inflatedVFReindexMap_value (S : Set M) {a b : ℕ} (f : Fin b → Fin a)
    (x : DefSet.univ (rawVFSpace (M := M) a) S) :
    (inflatedVFReindexMap S f x).val = x.val ∘ f := rfl

/-- The total value map `RV^n → (Γ ∪ {∞})^n`. -/
def inflatedRVGammaTopMap (S : Set M) (n : ℕ) :
    Map (DefSet.univ (rawRVSpace (M := M) n) S) (DefSet.univ (gammaTopSpace.power (Fin n)) S) := by
  let F (z : Fin n → M) : Fin n × Fin 1 → M := fun ij => z ij.1
  have hdom (c : (rawRVSpace (M := M) n).domain) : F c.val ∈ (gammaTopSpace.power (Fin n)).domain := by
    intro i
    change iRV (c.val i)
    rw [← congrFun (rvValues_decode c) i]
    exact ((rawRVSpace n).decode c i).property
  refine Map.ofCodes _ (fun x i => Values.vrv (x i)) F (fun _ => Set.DefinableFun.proj LRV) hdom ?_
  intro c
  funext i
  exact congrArg Values.vrv (Subtype.ext (congrFun (rvValues_decode c) i).symm)

@[simp] theorem inflatedRVGammaTopMap_value (S : Set M) (n : ℕ)
    (x : DefSet.univ (rawRVSpace (M := M) n) S) :
    (inflatedRVGammaTopMap S n x).val = fun i => Values.vrv (x.val i) := rfl

/-- The total valuation `VF^n → (Γ ∪ {∞})^n`. -/
def inflatedVFGammaTopMap (S : Set M) (n : ℕ) :
    Map (DefSet.univ (rawVFSpace (M := M) n) S) (DefSet.univ (gammaTopSpace.power (Fin n)) S) :=
  (inflatedRVGammaTopMap S n).comp (universalTupleRVMap S n)

@[simp] theorem inflatedVFGammaTopMap_value (S : Set M) (n : ℕ)
    (x : DefSet.univ (rawVFSpace (M := M) n) S) :
    (inflatedVFGammaTopMap S n x).val = fun i => Values.vrv (tupleRV x.val i) := rfl

/-- The inclusion `Γ^n → (Γ ∪ {∞})^n`. -/
def inflatedGammaIncludeMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (n : ℕ) :
    Map (DefSet.univ (inflatedGammaPower hc n) S) (DefSet.univ (gammaTopSpace.power (Fin n)) S) := by
  refine Map.ofCodes _ (fun γ i => (γ i).val) id (fun _ => Set.DefinableFun.proj LRV)
    (fun c i => (c.property i).1) ?_
  intro c
  rfl

@[simp] theorem inflatedGammaIncludeMap_value (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (n : ℕ)
    (x : DefSet.univ (inflatedGammaPower hc n) S) :
    (inflatedGammaIncludeMap hc S n x).val = fun i => (x.val i).val := rfl

/-! ### First-order operations on Gamma-ground sets -/

theorem _root_.DiamondIntegral.Section3.GammaGroundDefinable.diagonal_preimage {X Y : Space LRV M}
    (f g : Map (DefSet.univ X B.real) (DefSet.univ Y B.real)) :
    GammaGroundDefinable hc B X {x | (f ⟨x, Set.mem_univ _⟩).val = (g ⟨x, Set.mem_univ _⟩).val} := by
  have hEq : GammaGroundDefinable hc B (Y.prod Y) {z | z.1 = z.2} :=
    GammaGroundDefinable.of_real ((relationDefinable_iff_product Eq).mp (Y.relation_eq_definable B.real))
  exact hEq.preimage ((f.pair g).toUniv)

theorem _root_.DiamondIntegral.Section3.GammaGroundDefinable.forall_snd {P Q : Space LRV M} {S : Set (P.prod Q).Carrier}
    (hS : GammaGroundDefinable hc B (P.prod Q) S) :
    GammaGroundDefinable hc B P {p | ∀ q, (p, q) ∈ S} := by
  apply (hS.compl.image (universalProductFst P Q B.real)).compl.congr
  intro p
  constructor
  · intro h q
    by_contra hq
    exact h ⟨(p, q), hq, rfl⟩
  · rintro h ⟨z, hz, hzp⟩
    apply hz
    have he : z = (p, z.2) := Prod.ext hzp rfl
    rw [he]
    exact h z.2

theorem _root_.DiamondIntegral.Section3.GammaGroundDefinable.exists_snd {P Q : Space LRV M} {S : Set (P.prod Q).Carrier}
    (hS : GammaGroundDefinable hc B (P.prod Q) S) :
    GammaGroundDefinable hc B P {p | ∃ q, (p, q) ∈ S} := by
  apply (hS.image (universalProductFst P Q B.real)).congr
  intro p
  constructor
  · rintro ⟨z, hz, hzp⟩
    refine ⟨z.2, ?_⟩
    have he : (p, z.2) = z := Prod.ext hzp.symm rfl
    rw [he]
    exact hz
  · rintro ⟨q, hq⟩
    exact ⟨(p, q), hq, rfl⟩

/-- A value condition followed by a Gamma family: the Gamma tuple is the
unique one whose image in `Γ ∪ {∞}` is the given total value tuple. -/
theorem _root_.DiamondIntegral.Section3.GammaGroundDefinable.exists_gamma_lift {n : ℕ} {X Q : Space LRV M}
    {S : Set ((inflatedGammaPower hc n).prod Q).Carrier}
    (hS : GammaGroundDefinable hc B ((inflatedGammaPower hc n).prod Q) S)
    (φ : Map (DefSet.univ X B.real) (DefSet.univ (gammaTopSpace.power (Fin n)) B.real))
    (ψ : Map (DefSet.univ X B.real) (DefSet.univ Q B.real)) :
    GammaGroundDefinable hc B X {x | ∃ γ : Fin n → Values.Gamma (M := M),
      (∀ i, (φ ⟨x, Set.mem_univ _⟩).val i = (γ i).val) ∧ (γ, (ψ ⟨x, Set.mem_univ _⟩).val) ∈ S} := by
  let fst := universalProductFst X (inflatedGammaPower hc n) B.real
  let snd := universalProductSnd X (inflatedGammaPower hc n) B.real
  have h1 := GammaGroundDefinable.diagonal_preimage (hc := hc) (B := B)
    (φ.comp fst) ((inflatedGammaIncludeMap hc B.real n).comp snd)
  have h2 := hS.preimage ((snd.pair (ψ.comp fst)).toUniv)
  apply ((h1.inter h2).image fst).congr
  intro x
  constructor
  · rintro ⟨⟨x', γ⟩, ⟨he, hs⟩, hx⟩
    change x' = x at hx
    subst hx
    exact ⟨γ, fun i => congrFun he i, hs⟩
  · rintro ⟨γ, he, hs⟩
    exact ⟨(x, γ), ⟨funext he, hs⟩, rfl⟩

/-! ### Rows of Gamma families -/

/-- A Gamma tuple all of whose coordinates are definable over the base is
a definable point of `Γ^n`. -/
theorem inflatedGamma_singleton_definable {n : ℕ} {γ : Fin n → Values.Gamma (M := M)}
    (hγ : ∀ i, GammaDefinableClosureAtBase B (γ i)) :
    GammaGroundDefinable hc B (inflatedGammaPower hc n) {γ} := by
  apply (Section4.Section3GammaCodeBridge.native_iff (hc := hc) (B := B) {γ}).mpr
  have h := DefinableOverBase.finite_iInter (B := B) (sn := fun _ : Fin n => SortTag.rv) Finset.univ
    (fun i => {z : Fin n → M | z ∘ (fun _ : Fin 1 => i) ∈ {w : Fin 1 → M | w 0 ∈ Values.gammaPullback {γ i}} ∧
      z ∈ sortedUniverse (fun _ : Fin n => SortTag.rv)})
    (fun i _ => (hγ i).preimage_real (fun _ : Fin n => SortTag.rv) (fun _ : Fin 1 => i))
  unfold Section4.GammaOrderLogic.GammaDefinable
  convert h using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Finset.mem_univ, true_implies, Function.comp_apply]
  constructor
  · rintro ⟨hz, he⟩
    refine ⟨fun i => (hz i).1, fun i => ⟨?_, fun j => (hz j).1⟩⟩
    exact (gammaPullback_mem_codeValue_iff {γ i} (z i) (hz i)).mpr (congrFun he i)
  · rintro ⟨_, h⟩
    have hz : Proper z := fun i => by
      obtain ⟨hr, h0, _⟩ := (h i).1
      exact ⟨hr, h0⟩
    refine ⟨hz, funext fun i => ?_⟩
    exact (gammaPullback_mem_codeValue_iff {γ i} (z i) (hz i)).mp (h i).1

/-- The row of a family at a definable point of the parameter space. -/
theorem _root_.DiamondIntegral.Section3.GammaGroundDefinable.gammaFibre {C : Base (M := M)} {n : ℕ} {Q : Space LRV M}
    {S : Set ((inflatedGammaPower hc n).prod Q).Carrier}
    (hS : GammaGroundDefinable hc C ((inflatedGammaPower hc n).prod Q) S)
    {γ : Fin n → Values.Gamma (M := M)} (hγ : GammaGroundDefinable hc C (inflatedGammaPower hc n) {γ}) :
    GammaGroundDefinable hc C Q {x | (γ, x) ∈ S} := by
  apply ((hS.inter (hγ.preimage (universalProductFst _ Q C.real))).image
    (universalProductSnd _ Q C.real)).congr
  intro x
  constructor
  · rintro ⟨z, ⟨hz, hzγ⟩, hzx⟩
    change z.1 = γ at hzγ
    have he : z = (γ, x) := Prod.ext hzγ hzx
    rw [he] at hz
    exact hz
  · intro hx
    exact ⟨(γ, x), ⟨hx, rfl⟩, rfl⟩

theorem adjoinGammaTuple_names {n : ℕ} (γ : Fin n → Values.Gamma (M := M)) :
    ∀ i, γ i ∈ (adjoinGammaTuple B γ).gamma := fun i => Or.inr ⟨i, rfl⟩

/-- The row at an arbitrary Gamma tuple, over the base with that tuple adjoined. -/
def _root_.DiamondIntegral.Section3.GammaGroundDefSet.gammaFibreOver {n : ℕ} {Q : Space LRV M}
    (U : GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod Q)) (γ : Fin n → Values.Gamma (M := M)) :
    GammaGroundDefSet hc (adjoinGammaTuple B γ) Q :=
  ⟨{x | (γ, x) ∈ U.carrier},
    (U.definable.monoBase (C := adjoinGammaTuple B γ) (Set.Subset.refl _) Set.subset_union_left).gammaFibre
      (GammaGroundDefinable.gammaTuple_singleton γ (adjoinGammaTuple_names γ))⟩

/-- The row at a Gamma tuple with definable coordinates, over the base itself. -/
def _root_.DiamondIntegral.Section3.GammaGroundDefSet.gammaFibre {n : ℕ} {Q : Space LRV M}
    (U : GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod Q)) (γ : Fin n → Values.Gamma (M := M))
    (hγ : ∀ i, GammaDefinableClosureAtBase B (γ i)) : GammaGroundDefSet hc B Q :=
  ⟨{x | (γ, x) ∈ U.carrier}, U.definable.gammaFibre (inflatedGamma_singleton_definable hγ)⟩

@[simp] theorem _root_.DiamondIntegral.Section3.GammaGroundDefSet.mem_gammaFibre {n : ℕ} {Q : Space LRV M}
    (U : GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod Q)) (γ : Fin n → Values.Gamma (M := M))
    (hγ : ∀ i, GammaDefinableClosureAtBase B (γ i)) (x : Q.Carrier) :
    x ∈ (U.gammaFibre γ hγ).carrier ↔ (γ, x) ∈ U.carrier := Iff.rfl

@[simp] theorem _root_.DiamondIntegral.Section3.GammaGroundDefSet.mem_gammaFibreOver {n : ℕ} {Q : Space LRV M}
    (U : GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod Q)) (γ : Fin n → Values.Gamma (M := M))
    (x : Q.Carrier) : x ∈ (U.gammaFibreOver γ).carrier ↔ (γ, x) ∈ U.carrier := Iff.rfl

/-! ### Inflation of RV families -/

/-- The RV value-fibre inflation `{(z,u) : z ∈ (RV^×)^n, (vrv z, u) ∈ U}`. -/
def _root_.DiamondIntegral.Section3.GammaGroundDefSet.gammaRVInflation {n r : ℕ}
    (U : GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod (rawRVSpace (M := M) r))) :
    GammaGroundDefSet hc B (rawRVSpace (M := M) (n + r)) :=
  ⟨{v | ∃ γ : Fin n → Values.Gamma (M := M), (∀ i, Values.vrv (v (Fin.castAdd r i)) = (γ i).val) ∧
      (γ, v ∘ Fin.natAdd n) ∈ U.carrier},
    U.definable.exists_gamma_lift
      ((inflatedRVGammaTopMap B.real n).comp (inflatedRVReindexMap B.real (Fin.castAdd r)))
      (inflatedRVReindexMap B.real (Fin.natAdd n))⟩

theorem _root_.DiamondIntegral.Section3.GammaGroundDefSet.mem_gammaRVInflation {n r : ℕ}
    (U : GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod (rawRVSpace (M := M) r)))
    (v : Fin (n + r) → CanonicalRV.RVSort M) :
    v ∈ U.gammaRVInflation.carrier ↔ ∃ γ : Fin n → Values.Gamma (M := M),
      (∀ i, Values.vrv (v (Fin.castAdd r i)) = (γ i).val) ∧ (γ, v ∘ Fin.natAdd n) ∈ U.carrier := Iff.rfl

theorem _root_.DiamondIntegral.Section3.GammaGroundDefSet.append_mem_gammaRVInflation {n r : ℕ}
    (U : GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod (rawRVSpace (M := M) r)))
    (z : Fin n → CanonicalRV.RVSort M) (w : Fin r → CanonicalRV.RVSort M) :
    Fin.append z w ∈ U.gammaRVInflation.carrier ↔ ∃ γ : Fin n → Values.Gamma (M := M),
      (∀ i, Values.vrv (z i) = (γ i).val) ∧ (γ, w) ∈ U.carrier := by
  have hz : (fun i => Fin.append z w (Fin.castAdd r i)) = z := funext (Fin.append_left z w)
  have hw : Fin.append z w ∘ Fin.natAdd n = w := funext (Fin.append_right z w)
  constructor
  · rintro ⟨γ, hγ, hU⟩
    refine ⟨γ, fun i => ?_, hw ▸ hU⟩
    rw [← congrFun hz i]
    exact hγ i
  · rintro ⟨γ, hγ, hU⟩
    refine ⟨γ, fun i => ?_, hw.symm ▸ hU⟩
    rw [congrFun hz i]
    exact hγ i

/-- The Gamma tuple with prescribed total values is unique. -/
theorem inflated_gamma_unique {n : ℕ} {t : Fin n → Values.GammaTop (M := M)}
    {γ δ : Fin n → Values.Gamma (M := M)} (hγ : ∀ i, t i = (γ i).val) (hδ : ∀ i, t i = (δ i).val) :
    γ = δ :=
  funext fun i => Subtype.ext ((hγ i).symm.trans (hδ i))

/-! ### Gamma families of finite-RV-fibre VF objects -/

/-- A definable family `𝒜 ⊆ Γ^n × VF^m × RV^s` with finite RV fibres. -/
structure GammaVFFamily (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (n : ℕ) where
  m : ℕ
  s : ℕ
  domain : GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod (rawMixedSpace (M := M) m s))
  finite : ∀ (γ : Fin n → Values.Gamma (M := M)) (a : Fin m → Section2.VF M),
    {t | (γ, (a, t)) ∈ domain.carrier}.Finite

namespace GammaVFFamily
variable {n : ℕ} (A : GammaVFFamily hc B n)

/-- The row `A_γ`. -/
def row (γ : Fin n → Values.Gamma (M := M)) : Set (rawMixedSpace (M := M) A.m A.s).Carrier :=
  {q | (γ, q) ∈ A.domain.carrier}

/-- The row as an object over the base with the names `γ` adjoined. -/
def fibreOver (γ : Fin n → Values.Gamma (M := M)) : GammaGroundFiniteVFObject hc (adjoinGammaTuple B γ) where
  vfArity := A.m
  rvArity := A.s
  domain := A.domain.gammaFibreOver γ
  finite a := A.finite γ a

/-- The row at a Gamma tuple with definable coordinates, over the base. -/
def fibreAt (γ : Fin n → Values.Gamma (M := M)) (hγ : ∀ i, GammaDefinableClosureAtBase B (γ i)) :
    GammaGroundFiniteVFObject hc B where
  vfArity := A.m
  rvArity := A.s
  domain := A.domain.gammaFibre γ hγ
  finite a := A.finite γ a

theorem fibreAt_carrier (γ : Fin n → Values.Gamma (M := M)) (hγ : ∀ i, GammaDefinableClosureAtBase B (γ i)) :
    (A.fibreAt γ hγ).domain.carrier = A.row γ := rfl

theorem fibreOver_carrier (γ : Fin n → Values.Gamma (M := M)) :
    (A.fibreOver γ).domain.carrier = A.row γ := rfl

/-- The value-fibre inflation `{(x,a,t) : x ∈ (VF^×)^n, (vv x, a, t) ∈ 𝒜}` as a set. -/
def inflatedCarrier : Set (rawMixedSpace (M := M) (n + A.m) A.s).Carrier :=
  {p | ∃ γ : Fin n → Values.Gamma (M := M),
    (∀ i, Values.vrv (tupleRV (p.1 ∘ Fin.castAdd A.m) i) = (γ i).val) ∧
      (γ, (p.1 ∘ Fin.natAdd n, p.2)) ∈ A.domain.carrier}

/-- The full mixed projection used by the inflation. -/
def inflatedSplitMap (S : Set M) (n m s : ℕ) :
    Map (DefSet.univ (rawMixedSpace (M := M) (n + m) s) S) (DefSet.univ (rawMixedSpace (M := M) m s) S) :=
  (((inflatedVFReindexMap S (Fin.natAdd n)).comp (universalProductFst _ _ S)).pair
    (universalProductSnd _ _ S)).toUniv

/-- The value of the first `n` VF coordinates of a mixed tuple. -/
def inflatedValueMap (S : Set M) (n m s : ℕ) :
    Map (DefSet.univ (rawMixedSpace (M := M) (n + m) s) S) (DefSet.univ (gammaTopSpace.power (Fin n)) S) :=
  (inflatedVFGammaTopMap S n).comp ((inflatedVFReindexMap S (Fin.castAdd m)).comp (universalProductFst _ _ S))

theorem inflatedCarrier_definable :
    GammaGroundDefinable hc B (rawMixedSpace (M := M) (n + A.m) A.s) A.inflatedCarrier :=
  A.domain.definable.exists_gamma_lift (inflatedValueMap B.real n A.m A.s) (inflatedSplitMap B.real n A.m A.s)

theorem inflatedCarrier_finite (x : Fin (n + A.m) → Section2.VF M) :
    {t | (x, t) ∈ A.inflatedCarrier}.Finite := by
  by_cases h : ∃ γ : Fin n → Values.Gamma (M := M),
      ∀ i, Values.vrv (tupleRV (x ∘ Fin.castAdd A.m) i) = (γ i).val
  · obtain ⟨γ, hγ⟩ := h
    apply (A.finite γ (x ∘ Fin.natAdd n)).subset
    rintro t ⟨δ, hδ, ht⟩
    rw [inflated_gamma_unique hγ hδ]
    exact ht
  · convert Set.finite_empty
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨δ, hδ, _⟩
    exact h ⟨δ, hδ⟩

/-- The inflated total object `A^inf` over the original base. -/
def inflated : GammaGroundFiniteVFObject hc B where
  vfArity := n + A.m
  rvArity := A.s
  domain := ⟨A.inflatedCarrier, A.inflatedCarrier_definable⟩
  finite := A.inflatedCarrier_finite

theorem mem_inflated (p : (rawMixedSpace (M := M) (n + A.m) A.s).Carrier) :
    p ∈ A.inflated.domain.carrier ↔ ∃ γ : Fin n → Values.Gamma (M := M),
      (∀ i, Values.vrv (tupleRV (p.1 ∘ Fin.castAdd A.m) i) = (γ i).val) ∧
        p.1 ∘ Fin.natAdd n ∈ {a | (a, p.2) ∈ A.row γ} := Iff.rfl

/-- The value coordinates of a point of `A^inf` are nonzero. -/
theorem inflated_coordinate_ne_zero {p : (rawMixedSpace (M := M) (n + A.m) A.s).Carrier}
    (hp : p ∈ A.inflated.domain.carrier) (i : Fin n) : p.1 (Fin.castAdd A.m i) ≠ 0 := by
  obtain ⟨γ, hγ, _⟩ := hp
  intro h0
  apply (γ i).property
  rw [← hγ i, Values.vrv_eq_infinity_iff]
  change iRv (p.1 (Fin.castAdd A.m i)).val = iRVZero
  exact (CanonicalRV.encodedRv_zero_iff _).mpr h0

end GammaVFFamily

end DiamondIntegral.Section5
