import «section 7».Lemma714Ident

/-! Lemma 7.14, part 19: base maps times the identity on extra RV labels.

The freezing step of Lemma 7.14 prepares the common VF projection `P` of
`A'` and `A''` by a map `g : P → Q` (`P ⊆ VF`, `Q ⊆ VF × RV^s`), and acts on
`A ⊆ VF × RV^r` by `g ⋉ A : (a, u) ↦ (g(a)_VF, g(a)_RV ++ u)` (`prodMap`).
This file builds the map from the base projection and the code-level
assembly (`Map.ofCodes`, `Map.pair`), and proves the point formula
(`prodMap_apply`), injectivity and the label formula. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma714Prod
open DiamondIntegral.Section6 DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}

/-! ### The base projection -/

/-- The base point of a mixed point: forget the RV labels. -/
def basePoint (p : Mixed M 1 r) : Mixed M 1 0 := (p.1, Fin.elim0)

def baseCodes (z : Fin 1 ⊕ Fin r → M) : Fin 1 ⊕ Fin 0 → M := Sum.elim (z ∘ Sum.inl) Fin.elim0

/-- The base projection, as a definable map. -/
def baseProj (A : DefSet (rawMixedSpace (M := M) 1 r) S) : Map A (DefSet.univ (rawMixedSpace (M := M) 1 0) S) := by
  refine Map.ofCodes A basePoint baseCodes ?_ ?_ ?_
  · rintro (i | i)
    · exact Set.DefinableFun.proj LRV
    · exact i.elim0
  · intro c
    have h := mixedValues_mem_domain (M := M) (basePoint ((rawMixedSpace (M := M) 1 r).decode c))
    have e : (baseCodes c.val : Fin 1 ⊕ Fin 0 → M) = mixedValues (basePoint ((rawMixedSpace (M := M) 1 r).decode c)) := by
      funext i
      rcases i with i | i
      · exact (congrFun (mixedValues_decode c) (.inl i)).symm
      · exact i.elim0
    rw [e]
    exact h
  · intro c
    apply mixedValues_injective
    refine (mixedValues_decode _).trans ?_
    funext i
    rcases i with i | i
    · exact (congrFun (mixedValues_decode c) (.inl i)).symm
    · exact i.elim0

@[simp] theorem baseProj_apply (A : DefSet (rawMixedSpace (M := M) 1 r) S) (p : A) :
    (baseProj A p).val = basePoint p.val := rfl

/-! ### Code-level assembly -/

def assemblePoint (x : Mixed M 1 s × Mixed M 1 r) : Mixed M 1 (s + r) := (x.1.1, Fin.append x.1.2 x.2.2)

def assembleCodes (z : (Fin 1 ⊕ Fin s) ⊕ (Fin 1 ⊕ Fin r) → M) : Fin 1 ⊕ Fin (s + r) → M :=
  Sum.elim (fun i => z (.inl (.inl i))) (Fin.append (fun j => z (.inl (.inr j))) (fun j => z (.inr (.inr j))))

theorem mixedValues_assemble (x : Mixed M 1 s × Mixed M 1 r) :
    mixedValues (assemblePoint x) = assembleCodes (Sum.elim (mixedValues x.1) (mixedValues x.2)) := by
  funext i
  rcases i with i | i
  · rfl
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · simp [assemblePoint, assembleCodes, mixedValues, rvValues]
    · simp [assemblePoint, assembleCodes, mixedValues, rvValues]

/-- The assembly `((b, w), (a, u)) ↦ (b, w ++ u)`, as a definable map. -/
def assemble (C : DefSet ((rawMixedSpace (M := M) 1 s).prod (rawMixedSpace (M := M) 1 r)) S) :
    Map C (DefSet.univ (rawMixedSpace (M := M) 1 (s + r)) S) := by
  have hc : ∀ c : ((rawMixedSpace (M := M) 1 s).prod (rawMixedSpace (M := M) 1 r)).domain,
      (assembleCodes c.val : Fin 1 ⊕ Fin (s + r) → M) =
        mixedValues (assemblePoint (((rawMixedSpace (M := M) 1 s).prod (rawMixedSpace (M := M) 1 r)).decode c)) := by
    intro c
    rw [mixedValues_assemble]
    apply congrArg assembleCodes
    funext i
    rcases i with i | i
    · exact (congrFun (mixedValues_decode (⟨c.val ∘ Sum.inl, c.property.1⟩ : (rawMixedSpace (M := M) 1 s).domain)) i).symm
    · exact (congrFun (mixedValues_decode (⟨c.val ∘ Sum.inr, c.property.2⟩ : (rawMixedSpace (M := M) 1 r).domain)) i).symm
  refine Map.ofCodes C assemblePoint assembleCodes ?_ ?_ ?_
  · rintro (i | i)
    · exact Set.DefinableFun.proj LRV
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simp only [assembleCodes, Sum.elim_inr, Fin.append_left]
        exact Set.DefinableFun.proj LRV
      · simp only [assembleCodes, Sum.elim_inr, Fin.append_right]
        exact Set.DefinableFun.proj LRV
  · intro c
    rw [hc c]
    exact mixedValues_mem_domain _
  · intro c
    apply mixedValues_injective
    exact (mixedValues_decode _).trans (hc c)

@[simp] theorem assemble_apply (C : DefSet ((rawMixedSpace (M := M) 1 s).prod (rawMixedSpace (M := M) 1 r)) S)
    (x : C) : (assemble C x).val = assemblePoint x.val := rfl

/-! ### The product map -/

section Prod
variable {P : DefSet (rawMixedSpace (M := M) 1 0) S} {Q : DefSet (rawMixedSpace (M := M) 1 s) S}
  (g : Map P Q) {A : DefSet (rawMixedSpace (M := M) 1 r) S}
  (hAP : ∀ p ∈ A.carrier, basePoint p ∈ P.carrier)

/-- The base projection into `P`. -/
def baseMap : Map A P := (baseProj A).corestrict (fun p => hAP p.val p.property)

@[simp] theorem baseMap_apply (p : A) : (baseMap hAP p).val = basePoint p.val := rfl

/-- **`g ⋉ A`**: the base map times the identity on the RV labels of `A`. -/
def prodMap : Map A (DefSet.univ (rawMixedSpace (M := M) 1 (s + r)) S) :=
  (assemble _).comp ((g.comp (baseMap hAP)).pair (Map.id A))

theorem prodMap_apply (p : A) :
    (prodMap g hAP p).val = ((g (baseMap hAP p)).val.1, Fin.append (g (baseMap hAP p)).val.2 p.val.2) := rfl

theorem prodMap_labels (p : A) (i : Fin r) : (prodMap g hAP p).val.2 (Fin.natAdd s i) = p.val.2 i := by
  rw [prodMap_apply]
  exact Fin.append_right _ _ i

theorem prodMap_injective (hg : Function.Injective g) : Function.Injective (prodMap g hAP) := by
  intro p q he
  have he' := congrArg Subtype.val he
  rw [prodMap_apply, prodMap_apply] at he'
  have h1 := congrArg Prod.fst he'
  have h2 := congrArg Prod.snd he'
  have hw : (g (baseMap hAP p)).val.2 = (g (baseMap hAP q)).val.2 := by
    funext j
    have := congrFun h2 (Fin.castAdd r j)
    simpa only [Fin.append_left] using this
  have hu : p.val.2 = q.val.2 := by
    funext j
    have := congrFun h2 (Fin.natAdd s j)
    simpa only [Fin.append_right] using this
  have hgpq : g (baseMap hAP p) = g (baseMap hAP q) := Subtype.ext (Prod.ext h1 hw)
  have hb := congrArg (fun z : P => z.val.1) (hg hgpq)
  apply Subtype.ext
  exact Prod.ext hb hu

end Prod

end DiamondIntegral.Section7.Lemma714Prod
