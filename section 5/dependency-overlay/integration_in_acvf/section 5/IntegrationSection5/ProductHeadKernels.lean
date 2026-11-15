import IntegrationSection5.ProductRVBranchHead
import IntegrationSection5.ProductContractionKernels
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m l r b : ℕ}
variable {H : DefSet (M := M) S (n+1) l} {K : DefSet (M := M) S (n+1) r}

theorem lifted_headKey_eq_iff (f : Map H K) (hf : SpecialRelative f 0)
    (hle : l ≤ r) (σ : Fin b → Fin r)
    (hCover : ∀ j : Fin r, (∃ k, σ k = j) ∨ ∃ k, suffixIndex hle k = j) (p q : H) :
    headKey (f p).val = headKey (f q).val ↔ TailEq p.val q.val ∧
      SameRV (activeUnaryProjection 0 σ (f p).val) (activeUnaryProjection 0 σ (f q).val) ∧ p.val.2 = q.val.2 := by
  have hOther := specialRelative_unaryRelative hf
  constructor
  · intro he
    obtain ⟨ht,hSame⟩ := (headKey_eq_iff _ _).mp he
    refine ⟨fun j => (hOther p j.succ (Fin.succ_ne_zero j)).symm.trans ((ht j).trans (hOther q j.succ (Fin.succ_ne_zero j))),
      activeUnaryProjection_sameRV 0 σ hSame,?_⟩
    funext j
    exact (specialRelative_oldLabels hf p j).symm.trans
      ((congrFun ((sameRV_iff _ _).mp hSame).2 (suffixIndex hle j)).trans (specialRelative_oldLabels hf q j))
  · rintro ⟨ht,hSame,hOld⟩
    have htOut : TailEq (f p).val (f q).val := fun j =>
      (hOther p j.succ (Fin.succ_ne_zero j)).trans ((ht j).trans (hOther q j.succ (Fin.succ_ne_zero j)).symm)
    apply (headKey_eq_iff _ _).mpr
    refine ⟨htOut,?_⟩
    obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp hSame
    apply (sameRV_iff _ _).mpr
    refine ⟨fun i => ?_,?_⟩
    · cases i using Fin.cases with
      | zero => exact hv 0
      | succ j => exact congrArg rv (htOut j)
    · funext j
      rcases hCover j with ⟨k,rfl⟩ | ⟨k,rfl⟩
      · exact congrFun hl k
      · exact (specialRelative_oldLabels hf p k).trans
          ((congrFun hOld k).trans (specialRelative_oldLabels hf q k).symm)

namespace ProductRVBranchHead
variable {a b : ℕ} {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {R : DefSet (M := M) S (n+1) m} {u : SpecialBijection A B}
variable {ρ : Fin a → Fin l} {E : Set (Fin a → RV (M := M))} {previous : Option Bool}

theorem head_kernel (L : ProductRVBranchHead (G := G) u H ρ E previous)
    (h : Map R H) (d : Map R A)
    (hFlag : ∀ p : R, (h p).val.2 ∘ ρ ∈ E)
    (hSelect : ∀ p : R, (d p).val = activeUnaryProjection 0 ρ (h p).val)
    (hVF : ∀ p : R, ∀ i, vfAt (h p).val i = vfAt p.val i)
    (hOld : ∀ p q : R, SameRV (d p).val (d q).val → (h p).val.2 = (h q).val.2)
    (p q : R) :
    headKey (L.preparation.map (h p)).val = headKey (L.preparation.map (h q)).val ↔
      TailEq p.val q.val ∧ SameRV (u.toMap (d p)).val (u.toMap (d q)).val := by
  have hComm (p : R) : activeUnaryProjection 0 L.projection (L.preparation.map (h p)).val = (u.toMap (d p)).val := by
    have he : (⟨activeUnaryProjection 0 ρ (h p).val,L.embedding (h p).val (h p).property (hFlag p)⟩ : A) = d p :=
      Subtype.ext (hSelect p).symm
    exact (L.square (h p) (hFlag p)).trans (congrArg (fun a : A => (u.toMap a).val) he)
  rw [lifted_headKey_eq_iff L.preparation.map L.preparation.special L.arity_le L.projection L.coverage,hComm,hComm]
  constructor
  · rintro ⟨ht,hSame,_⟩
    exact ⟨fun j => (hVF p j.succ).symm.trans ((ht j).trans (hVF q j.succ)),hSame⟩
  · rintro ⟨ht,hSame⟩
    have hInput := u.inverse_contractible (u.toMap (d p)) (u.toMap (d q)) hSame
    rw [u.inverse_apply,u.inverse_apply] at hInput
    exact ⟨fun j => (hVF p j.succ).trans ((ht j).trans (hVF q j.succ).symm),hSame,hOld p q hInput⟩

end ProductRVBranchHead
end IntegrationInACVF.Section5
