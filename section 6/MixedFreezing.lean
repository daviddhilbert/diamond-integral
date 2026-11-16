import «section 6».OpenBallFreezing
import Section4.MapCorestrict

/-! Actual mixed-sort maps implementing FMT. Composition with a focus
map keeps its whole graph over S; the product-domain proof is attached
to that precise focus domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.FMT

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def mixedFamilyFreeze (A : Set (OpenBallCodes.OpenBall M)) (c : A → VF M)
    (i : Fin n) (p : Mixed M n r) : Mixed M n r :=
  (Function.update p.1 i (vfFamilyFreeze A c (p.1 i)),p.2)

def mixedFamilyFreezeCodes (A : Set (OpenBallCodes.OpenBall M)) (c : A → VF M)
    (i : Fin n) (z : Fin n ⊕ Fin r → M) : Fin n ⊕ Fin r → M :=
  Sum.elim (Function.update (z ∘ Sum.inl) i (rawFamilyFreeze A c (z (.inl i)))) (z ∘ Sum.inr)

theorem mixedFamilyFreeze_values (A : Set (OpenBallCodes.OpenBall M)) (c : A → VF M)
    (i : Fin n) (p : Mixed M n r) :
    mixedValues (mixedFamilyFreeze A c i p) = mixedFamilyFreezeCodes A c i (mixedValues p) := by
  funext j
  cases j with
  | inl j =>
    by_cases hj : j = i
    · subst j
      simp only [mixedValues,mixedFamilyFreeze,mixedFamilyFreezeCodes,Sum.elim_inl,vfValues,
        Function.update_self,vfFamilyFreeze]
    · simp only [mixedValues,mixedFamilyFreeze,mixedFamilyFreezeCodes,Sum.elim_inl,vfValues,
        Function.update_of_ne hj,Function.comp_apply]
  | inr j => rfl

def mixedFamilyFreezeMap
    (A : Set (OpenBallCodes.OpenBall M)) (c : A → VF M) (i : Fin n)
    (hsep : ∀ D E : A, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hAdef : S.Definable LRV (OpenBallCodes.pullback A))
    (hcdef : S.Definable LRV (OpenBallCodes.quotientCenterGraph A (fun D => (c D).val)))
    (C : DefSet (rawMixedSpace (M := M) n r) S) :
    Map C (DefSet.univ (rawMixedSpace (M := M) n r) S) := by
  let P := rawMixedSpace (M := M) n r
  let F : (Fin n ⊕ Fin r → M) → Fin n ⊕ Fin r → M := mixedFamilyFreezeCodes A c i
  have hF : S.DefinableMap LRV F := by
    rintro (j | j)
    · by_cases hj : j = i
      · subst j
        have h := (rawFamilyFreeze_definable A c hsep hAdef hcdef).comp
          (show S.DefinableMap LRV (fun z : Fin n ⊕ Fin r → M => fun _ : Fin 1 => z (.inl i)) from
            fun _ => Set.DefinableFun.proj LRV)
        simpa only [F,mixedFamilyFreezeCodes,Sum.elim_inl,Function.update_self] using h
      · simpa only [F,mixedFamilyFreezeCodes,Sum.elim_inl,Function.update_of_ne hj,Function.comp_apply]
          using (Set.DefinableFun.proj (L := LRV) (A := S) (i := (.inl j : Fin n ⊕ Fin r)))
    · exact Set.DefinableFun.proj LRV
  have hcode (z : P.domain) : mixedValues (mixedFamilyFreeze A c i (P.decode z)) = F z.val :=
    (mixedFamilyFreeze_values A c i (P.decode z)).trans (congrArg F (mixedValues_decode z))
  have hdom (z : P.domain) : F z.val ∈ P.domain := by
    rw [← hcode z]
    exact mixedValues_mem_domain _
  exact Map.ofCodes C (mixedFamilyFreeze A c i) F hF hdom
    (fun z => mixedValues_injective ((mixedValues_decode ⟨F z.val,hdom z⟩).trans (hcode z).symm))

def CoordinateProductDomain (C : Set (Mixed M n r)) (D : Set (VF M)) (c : VF M) (i : Fin n) : Prop :=
  ∀ p : Mixed M n r, p.1 i ∈ D → (p ∈ C ↔ (Function.update p.1 i c,p.2) ∈ C)

theorem mixedFamilyFreeze_mapsTo (A : Set (OpenBallCodes.OpenBall M)) (c : A → VF M)
    (i : Fin n) (C : Set (Mixed M n r))
    (hsep : ∀ D E : A, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hprod : ∀ D : A, CoordinateProductDomain C (vfOpenBall D.val) (c D) i) :
    Set.MapsTo (mixedFamilyFreeze A c i) C C := by
  intro p hp
  by_cases hx : ∃ D : A, p.1 i ∈ vfOpenBall D.val
  · obtain ⟨D,hD⟩ := hx
    have hf : vfFamilyFreeze A c (p.1 i) = c D := by
      rw [vfFamilyFreeze_eq A c hsep]
      exact familyFreeze_inside _ _ (fun D E x hx hE => hsep D E x.val hx hE) D _ hD
    simpa only [mixedFamilyFreeze,hf] using (hprod D p hD).mp hp
  · have hf : vfFamilyFreeze A c (p.1 i) = p.1 i := by
      rw [vfFamilyFreeze_eq A c hsep]
      exact familyFreeze_outside _ _ _ (not_exists.mp hx)
    simpa only [mixedFamilyFreeze,hf,Function.update_eq_self,Prod.mk.eta] using hp

def frozenFocusMap
    (A : Set (OpenBallCodes.OpenBall M)) (c : A → VF M) (i : Fin n)
    (hsep : ∀ D E : A, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E)
    (hAdef : S.Definable LRV (OpenBallCodes.pullback A))
    (hcdef : S.Definable LRV (OpenBallCodes.quotientCenterGraph A (fun D => (c D).val)))
    {C : DefSet (rawMixedSpace (M := M) n r) S}
    (hprod : ∀ D : A, CoordinateProductDomain C.carrier (vfOpenBall D.val) (c D) i)
    {B : DefSet (rawVFSpace (M := M) 1) S} (f : Map C B) : Map C B :=
  f.comp ((mixedFamilyFreezeMap A c i hsep hAdef hcdef C).corestrict
    (fun p => mixedFamilyFreeze_mapsTo A c i C.carrier hsep hprod p.property))

end DiamondIntegral.Section6.FMT
