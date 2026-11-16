import «section 6».RepairedFocusSteps

/-! Actual original-base VF-coordinate relabeling. Its inverse and
full image are explicit; proper invariance, double bounds, taggedness
and RV-pullbacks are transported without changing the parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def reindexVFPoint (e : Fin n ≃ Fin n) (p : Mixed M n r) : Mixed M n r := (p.1 ∘ e,p.2)

theorem reindexVFPoint_inverse (e : Fin n ≃ Fin n) (p : Mixed M n r) :
    reindexVFPoint e.symm (reindexVFPoint e p) = p := by
  apply Prod.ext
  · funext i
    exact congrArg p.1 (e.apply_symm_apply i)
  · rfl

def reindexVFMap (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Fin n ≃ Fin n) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n r) S) := by
  let P := rawMixedSpace (M := M) n r
  let codes (z : Fin n ⊕ Fin r → M) : Fin n ⊕ Fin r → M :=
    Sum.elim (fun i => z (.inl (e i))) (z ∘ Sum.inr)
  have hcodes : S.DefinableMap LRV codes := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hcode (z : P.domain) : mixedValues (reindexVFPoint e (P.decode z)) = codes z.val := by
    have he := mixedValues_decode z
    funext i
    cases i with
    | inl i => exact congrFun he (.inl (e i))
    | inr i => exact congrFun he (.inr i)
  have hdom (z : P.domain) : codes z.val ∈ P.domain := by
    rw [← hcode z]
    exact mixedValues_mem_domain _
  exact Map.ofCodes A (reindexVFPoint e) codes hcodes hdom
    (fun z => mixedValues_injective ((mixedValues_decode ⟨_,hdom z⟩).trans (hcode z).symm))

def reindexedVFSet (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Fin n ≃ Fin n) :=
  (reindexVFMap A e).image

theorem mem_reindexedVFSet (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Fin n ≃ Fin n)
    (q : Mixed M n r) : q ∈ (reindexedVFSet A e).carrier ↔ reindexVFPoint e.symm q ∈ A.carrier := by
  constructor
  · rintro ⟨p,hp⟩
    change reindexVFPoint e p.val = q at hp
    rw [← hp,reindexVFPoint_inverse]
    exact p.property
  · intro hq
    refine ⟨⟨reindexVFPoint e.symm q,hq⟩,?_⟩
    exact reindexVFPoint_inverse e.symm q

theorem reindexedVFSet_properInvariant
    (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Fin n ≃ Fin n)
    (hA : ProperInvariant S A.carrier) : ProperInvariant S (reindexedVFSet A e).carrier := by
  obtain ⟨γ,hγ⟩ := hA.vfBounded
  obtain ⟨δ,hδ⟩ := hA.rvBounded
  refine ⟨(reindexedVFSet A e).definable,⟨γ,?_⟩,⟨δ,?_⟩,fun u => ?_⟩
  · intro p hp i
    have hm := (mem_reindexedVFSet A e p).mp hp
    simpa only [reindexVFPoint,Function.comp_apply,Equiv.symm_apply_apply] using
      hγ _ hm (e i)
  · intro p hp i
    exact hδ _ ((mem_reindexedVFSet A e p).mp hp) i
  · obtain ⟨α,hα,hInv⟩ := hA.radii u
    refine ⟨α ∘ e,fun i => hα (e i),fun a b hab => ?_⟩
    have hClose : Congruent α (a ∘ e.symm) (b ∘ e.symm) := by
      intro i
      simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hab (e.symm i)
    exact (mem_reindexedVFSet A e (a,u)).trans
      ((hInv _ _ hClose).trans (mem_reindexedVFSet A e (b,u)).symm)

theorem reindexedVFSet_doublyBounded
    (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Fin n ≃ Fin n)
    (hA : VFDoublyBounded A.carrier) : VFDoublyBounded (reindexedVFSet A e).carrier := by
  obtain ⟨γ,hγ⟩ := hA
  refine ⟨γ,fun p hp i => ?_⟩
  simpa only [reindexVFPoint,Function.comp_apply,Equiv.symm_apply_apply] using
    hγ _ ((mem_reindexedVFSet A e p).mp hp) (e i)

theorem reindexedVFSet_rvPullback
    (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Fin n ≃ Fin n)
    (hA : IsRVPullback A.carrier) : IsRVPullback (reindexedVFSet A e).carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
  apply (mem_reindexedVFSet A e q).mpr
  exact rvPullback_mem_of_sameRV hA ((mem_reindexedVFSet A e p).mp hp)
    (funext (fun i => congrFun hVF (e.symm i))) hRV

def lastHeadIndices (n : ℕ) : Fin (n+1) ≃ Fin (n+1) where
  toFun := Fin.cases (Fin.last n) Fin.castSucc
  invFun := Fin.lastCases 0 Fin.succ
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem reindexVFPoint_lastHead (p : Mixed M (n+1) r) :
    reindexVFPoint (lastHeadIndices n) p = (Fin.cons (p.1 (Fin.last n)) (Fin.init p.1),p.2) := by
  apply Prod.ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  · rfl

theorem reindexVFPoint_lastHead_snoc (b : Fin n → VF M) (x : VF M) (u : Fin r → RVInfinity M) :
    reindexVFPoint (lastHeadIndices n) (Fin.snoc b x,u) = (Fin.cons x b,u) := by
  rw [reindexVFPoint_lastHead]
  simp only [Fin.snoc_last,Fin.init_snoc]

end DiamondIntegral.Section6
