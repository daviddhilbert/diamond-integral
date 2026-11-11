import «section 2».Conventions
import Section4.TupleFamilies
import Section4.RealPresentations
import Section8.RVLocalConstancy

/-!
# Uniform RV labels for the finite branches in Lemma 2.44

The existing checked tuple-family code supplies one uniform RV arity and
an injective code on every finite fibre. All graphs use the original real
base. Empty fibres and the absorbing-zero RV tag are retained.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

def vfCorrespondenceGraph (A : Set (Fin n → VF M))
    (F : (Fin n → VF M) → Set (Fin m → VF M)) : Set (Fin n ⊕ Fin m → M) :=
  {z | ∃ a ∈ A, ∃ y ∈ F a, Sum.elim (vfValues a) (vfValues y) = z}

structure FinitaryRVCode (S : Set M) (A : Set (Fin n → VF M))
    (F : (Fin n → VF M) → Set (Fin m → VF M)) where
  arity : ℕ
  code : (Fin n → M) → (Fin m → M) → Fin arity → M
  definable : ∀ j, S.DefinableFun LRV
    (fun z : Fin n ⊕ Fin m → M => code (z ∘ Sum.inl) (z ∘ Sum.inr) j)
  sorted : ∀ a (y : Fin m → VF M) j, iRV (code a (vfValues y) j)
  injective : ∀ a ∈ A, Set.InjOn (fun y => code (vfValues a) (vfValues y)) (F a)

theorem exists_finitaryRVCode
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin n → VF M)) (F : (Fin n → VF M) → Set (Fin m → VF M))
    (hG : S.Definable LRV (vfCorrespondenceGraph A F))
    (hfin : ∀ a ∈ A, (F a).Finite) : Nonempty (FinitaryRVCode S A F) := by
  classical
  let R : Set ((Fin n → M) × (Fin m → VF M)) :=
    {p | ∃ a ∈ A, vfValues a = p.1 ∧ p.2 ∈ F a}
  have hR : TupleFamilies.RelationDefinable S R := by
    change S.Definable LRV {z : Fin n ⊕ Fin m → M |
      ∃ y, (z ∘ Sum.inl, y) ∈ R ∧ vfValues y = z ∘ Sum.inr}
    convert hG using 1
    ext z
    constructor
    · rintro ⟨y, ⟨a, ha, hx, hy⟩, he⟩
      refine ⟨a, ha, y, hy, ?_⟩
      funext i
      cases i with
      | inl i => exact congrFun hx i
      | inr i => exact congrFun he i
    · rintro ⟨a, ha, y, hy, he⟩
      exact ⟨y, ⟨a, ha, funext (fun i => congrFun he (.inl i)), hy⟩,
        funext (fun i => congrFun he (.inr i))⟩
  have hRfin (t : Fin n → M) : {y | (t, y) ∈ R}.Finite := by
    by_cases ht : ∃ a ∈ A, vfValues a = t
    · obtain ⟨a, ha, hat⟩ := ht
      apply (hfin a ha).subset
      rintro y ⟨b, hb, hbt, hy⟩
      have hba : b = a := vfValues_injective (hbt.trans hat.symm)
      exact hba ▸ hy
    · have he : {y | (t, y) ∈ R} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro y ⟨a, ha, hat, _⟩
        exact ht ⟨a, ha, hat⟩
      rw [he]
      exact Set.finite_empty
  obtain ⟨d, hinj, hdef, hsort⟩ := TupleFamilies.uniform_coding h00 hs S hsmall R hR hRfin
  refine ⟨⟨m*d, TupleFamilies.code d R hRfin, hdef, hsort, ?_⟩⟩
  intro a ha y hy z hz he
  exact hinj (vfValues a) ⟨a, ha, rfl, hy⟩ ⟨a, ha, rfl, hz⟩ he

namespace FinitaryRVCode
variable {S : Set M} {A : Set (Fin n → VF M)}
variable {F : (Fin n → VF M) → Set (Fin m → VF M)}

def labelGraph (C : FinitaryRVCode S A F) : Set (Fin n ⊕ Fin C.arity → M) :=
  {z | ∃ a ∈ A, ∃ y ∈ F a,
    vfValues a = z ∘ Sum.inl ∧ C.code (vfValues a) (vfValues y) = z ∘ Sum.inr}

omit hM in
theorem mem_labelGraph (C : FinitaryRVCode S A F)
    (a : Fin n → VF M) (t : Fin C.arity → M) :
    Sum.elim (vfValues a) t ∈ C.labelGraph ↔
      a ∈ A ∧ ∃ y ∈ F a, C.code (vfValues a) (vfValues y) = t := by
  constructor
  · rintro ⟨b, hb, y, hy, he, ht⟩
    have hba : b = a := vfValues_injective he
    subst b
    exact ⟨hb, y, hy, ht⟩
  · rintro ⟨ha, y, hy, ht⟩
    exact ⟨a, ha, y, hy, rfl, ht⟩

omit hM in
theorem labelGraph_definable (C : FinitaryRVCode S A F)
    (hG : S.Definable LRV (vfCorrespondenceGraph A F)) :
    S.Definable LRV C.labelGraph := by
  let W := (Fin n ⊕ Fin m) ⊕ Fin C.arity
  let π : Fin n ⊕ Fin C.arity → W := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have hcode (j : Fin C.arity) : S.Definable LRV
      {z : W → M | z (.inr j) =
        C.code ((z ∘ Sum.inl) ∘ Sum.inl) ((z ∘ Sum.inl) ∘ Sum.inr) j} :=
    (Set.DefinableFun.proj LRV).ofPred_eq
      ((C.definable j).comp (fun _ => Set.DefinableFun.proj LRV))
  have h := ((hG.preimage_comp (Sum.inl : Fin n ⊕ Fin m → W)).inter
    (Set.definable_iInter_of_finite hcode)).image_comp π
  convert h using 1
  ext z
  constructor
  · rintro ⟨a, ha, y, hy, hax, hyt⟩
    let w : W → M := Sum.elim (Sum.elim (vfValues a) (vfValues y))
      (C.code (vfValues a) (vfValues y))
    refine ⟨w, ⟨⟨a, ha, y, hy, rfl⟩, ?_⟩, ?_⟩
    · simp only [Set.mem_iInter]
      exact fun _ => rfl
    · funext i
      cases i with
      | inl i => exact congrFun hax i
      | inr i => exact congrFun hyt i
  · rintro ⟨w, ⟨⟨a, ha, y, hy, he⟩, hw⟩, hp⟩
    have hax : vfValues a = z ∘ Sum.inl := by
      funext i
      exact (congrFun he (.inl i)).trans (congrFun hp (.inl i))
    refine ⟨a, ha, y, hy, hax, ?_⟩
    have hc (j : Fin C.arity) := Set.mem_iInter.mp hw j
    have hl : w ∘ Sum.inl = Sum.elim (vfValues a) (vfValues y) := he.symm
    funext j
    have hj := hc j
    change w (.inr j) = C.code ((w ∘ Sum.inl) ∘ Sum.inl)
      ((w ∘ Sum.inl) ∘ Sum.inr) j at hj
    rw [hl] at hj
    exact hj.symm.trans (congrFun hp (.inr j))

noncomputable def typedCode (C : FinitaryRVCode S A F) (a : Fin n → VF M)
    (y : Fin m → VF M) : Fin C.arity → RVInfinity M :=
  fun j => ⟨C.code (vfValues a) (vfValues y) j, C.sorted _ _ j⟩

omit hM in
theorem labelFibre_eq_image (C : FinitaryRVCode S A F) (a : Fin n → VF M) (ha : a ∈ A) :
    rvFibre C.labelGraph a = C.typedCode a '' F a := by
  ext t
  rw [rvFibre, Set.mem_ofPred_eq, C.mem_labelGraph, and_iff_right ha]
  constructor
  · rintro ⟨y, hy, ht⟩
    exact ⟨y, hy, funext (fun j => Subtype.ext (congrFun ht j))⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

end FinitaryRVCode
end DiamondIntegral.Section2
