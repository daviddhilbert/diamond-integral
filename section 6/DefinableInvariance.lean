import «section 6».InvariantHull
import Section4.RealPresentations

/-! Definition 6.2 and Lemma 6.6 over the original real parameter base.
Radius names are full invariant RV preimages of actual Gamma singletons.
No representative or center is adjoined to the ground base. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

def hullRVCode (z : Fin n ⊕ Fin m → M) : Fin n ⊕ Fin m → M :=
  Sum.elim (fun i => iRv (z (.inl i))) (fun j => z (.inr j))

theorem hullRVCode_definable (S : Set M) :
    S.DefinableMap LRV (hullRVCode (M := M) (n := n) (m := m)) := by
  rintro (i | j)
  · exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun z : Fin n ⊕ Fin m → M => ![z (.inl i)]) from by
        intro k
        fin_cases k
        exact Set.DefinableFun.proj LRV)
  · exact Set.DefinableFun.proj LRV

theorem hullRVCode_eq_iff (p q : Mixed M n m) :
    hullRVCode (mixedValues p) = hullRVCode (mixedValues q) ↔
      tupleRV M p.1 = tupleRV M q.1 ∧ p.2 = q.2 := by
  constructor
  · intro he
    constructor
    · funext i
      exact Subtype.ext (congrFun he (.inl i))
    · funext j
      exact Subtype.ext (congrFun he (.inr j))
  · rintro ⟨hVF,hRV⟩
    funext i
    cases i with
    | inl i => exact congrArg Subtype.val (congrFun hVF i)
    | inr j => exact congrArg (fun t => (t j).val) hRV

theorem rvHull_definable (S : Set M) (A : Set (Mixed M n m))
    (hA : (rawMixedSpace (M := M) n m).Definable S A) :
    (rawMixedSpace (M := M) n m).Definable S (rvHull A) := by
  let P := rawMixedSpace (M := M) n m
  let I := Fin n ⊕ Fin m
  let F := hullRVCode (M := M) (n := n) (m := m)
  have hF := hullRVCode_definable (M := M) (n := n) (m := m) S
  have heq : S.Definable LRV {z : I ⊕ I → M | F (z ∘ Sum.inr) = F (z ∘ Sum.inl)} := by
    have heach (i : I) : S.Definable LRV
        {z : I ⊕ I → M | F (z ∘ Sum.inr) i = F (z ∘ Sum.inl) i} :=
      ((hF i).comp (fun _ => Set.DefinableFun.proj LRV)).ofPred_eq
        ((hF i).comp (fun _ => Set.DefinableFun.proj LRV))
    convert Set.definable_iInter_of_finite heach using 1
    ext z
    simp only [Set.mem_iInter,Set.mem_ofPred_eq,funext_iff]
    rfl
  have hrel := (hA.preimage_comp (Sum.inr : I → I ⊕ I)).inter heq
  have hex := hrel.exists_of_finite
  have hout := (P.definable_domain S).inter hex
  change S.Definable LRV (P.preimage (rvHull A))
  convert hout using 1
  ext z
  change (∃ hz : z ∈ P.domain, P.decode ⟨z,hz⟩ ∈ rvHull A) ↔
    z ∈ P.domain ∧ ∃ q : I → M, q ∈ P.preimage A ∧ F q = F z
  constructor
  · rintro ⟨hz,h⟩
    obtain ⟨a,ha,hVF,hRV⟩ := (mem_rvHull_iff A (P.decode ⟨z,hz⟩)).mp h
    refine ⟨hz,mixedValues a,?_,?_⟩
    · exact ⟨mixedValues_mem_domain a,by simpa only [P,decode_mixedValues] using ha⟩
    · exact ((hullRVCode_eq_iff _ _).mpr ⟨hVF,hRV⟩).trans
        (congrArg F (mixedValues_decode (M := M) ⟨z,hz⟩))
  · rintro ⟨hz,q,⟨hq,hqa⟩,he⟩
    refine ⟨hz,(mem_rvHull_iff A (P.decode ⟨z,hz⟩)).mpr
      ⟨P.decode ⟨q,hq⟩,hqa,?_⟩⟩
    apply (hullRVCode_eq_iff _ _).mp
    exact (congrArg F (mixedValues_decode (M := M) ⟨q,hq⟩)).trans
      (he.trans (congrArg F (mixedValues_decode (M := M) ⟨z,hz⟩)).symm)

def NamedRadii (S : Set M) (t : Fin m → RVInfinity M) (α : Fin n → Gamma M) : Prop :=
  ∀ i, (S ∪ Set.range (rvValues t)).Definable LRV
    {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α i}}

theorem NamedRadii.max {S : Set M} {t : Fin m → RVInfinity M}
    {α β : Fin n → Gamma M} (hα : NamedRadii S t α) (hβ : NamedRadii S t β) :
    NamedRadii S t (fun i => max (α i) (β i)) := by
  intro i
  rcases le_total (α i) (β i) with h | h
  · simpa only [max_eq_right h] using hβ i
  · simpa only [max_eq_left h] using hα i

/-- The manuscript's proper invariant sets, retaining original-base
definability of the set and t-definability of each finite Gamma radius. -/
structure ProperInvariant (S : Set M) (A : Set (Mixed M n m)) : Prop where
  definable : (rawMixedSpace (M := M) n m).Definable S A
  vfBounded : VFBounded A
  rvBounded : RVSupportDoublyBounded A
  radii : ∀ t : Fin m → RVInfinity M, ∃ α : Fin n → Gamma M,
    NamedRadii S t α ∧ AlphaInvariant α (vfFibre A t)

theorem ProperInvariant.geometry {S : Set M} {A : Set (Mixed M n m)}
    (hA : ProperInvariant S A) : ProperInvariantGeometry A :=
  ⟨hA.vfBounded,hA.rvBounded,fun t => by
    obtain ⟨α,_,hα⟩ := hA.radii t
    exact ⟨α,hα⟩⟩

theorem ProperInvariant.rvHull {S : Set M} {A : Set (Mixed M n m)}
    (hA : ProperInvariant S A) : ProperInvariant S (rvHull A) := by
  refine ⟨rvHull_definable S A hA.definable,hA.vfBounded.rvHull,
    hA.rvBounded.rvHull,fun t => ?_⟩
  obtain ⟨α,hdef,hα⟩ := hA.radii t
  refine ⟨α,hdef,?_⟩
  rw [vfFibre_rvHull]
  exact hα.rvSaturation

theorem ProperInvariant.inter {S : Set M} {A B : Set (Mixed M n m)}
    (hA : ProperInvariant S A) (hB : ProperInvariant S B) : ProperInvariant S (A ∩ B) := by
  refine ⟨hA.definable.inter _ hB.definable,
    hA.vfBounded.mono Set.inter_subset_left,hA.rvBounded.mono Set.inter_subset_left,fun t => ?_⟩
  obtain ⟨α,hαdef,hα⟩ := hA.radii t
  obtain ⟨β,hβdef,hβ⟩ := hB.radii t
  exact ⟨fun i => max (α i) (β i),hαdef.max hβdef,hα.inter hβ⟩

theorem ProperInvariant.diff {S : Set M} {A B : Set (Mixed M n m)}
    (hA : ProperInvariant S A) (hB : ProperInvariant S B) : ProperInvariant S (A \ B) := by
  refine ⟨hA.definable.sdiff _ hB.definable,
    hA.vfBounded.mono Set.sdiff_subset,hA.rvBounded.mono Set.sdiff_subset,fun t => ?_⟩
  obtain ⟨α,hαdef,hα⟩ := hA.radii t
  obtain ⟨β,hβdef,hβ⟩ := hB.radii t
  exact ⟨fun i => max (α i) (β i),hαdef.max hβdef,hα.diff hβ⟩

/-- Lemma 6.6 (`int:inv`), with all original-base and radius hypotheses.
The result does not assert finite RV fibers for the hull complement. -/
theorem lemma_6_6 {S : Set M} {A B : Set (Mixed M n m)}
    (hA : ProperInvariant S A) (hB : ProperInvariant S B) :
    ProperInvariant S (A ∩ B) ∧
      ProperInvariant S (DiamondIntegral.Section2.rvHull A \ A) ∧
      ProperInvariant S (B \ A) :=
  ⟨hA.inter hB,hA.rvHull.diff hA,hB.diff hA⟩

end DiamondIntegral.Section6
