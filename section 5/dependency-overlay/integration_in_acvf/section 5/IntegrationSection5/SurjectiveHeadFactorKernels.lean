import IntegrationSection5.ProductHeadKernels
import IntegrationSection5.GammaPointSurjectiveDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m l b : ℕ}
variable {A : DefSet (M := M) S (n+1) m} {B : DefSet (M := M) S (n+1) l}
variable {D : DefSet (M := M) S 1 b}

theorem surjective_head_factor_kernel (f : Map A B) (hf : SpecialRelative f 0)
    (σ : Fin b → Fin l) (hσ : Function.Surjective σ) (d : Map A D)
    (hFactor : ∀ p : A, activeUnaryProjection 0 σ (f p).val = (d p).val) (p q : A) :
    headKey (f p).val = headKey (f q).val ↔ TailEq p.val q.val ∧ SameRV (d p).val (d q).val := by
  have hOther := specialRelative_unaryRelative hf
  constructor
  · intro he
    have ht := ((headKey_eq_iff _ _).mp he).1
    have hL := (headKey_labels_projection_iff σ hσ (f p).val (f q).val).mp (congrArg Prod.snd he)
    rw [hFactor,hFactor] at hL
    exact ⟨fun j => (hOther p j.succ (Fin.succ_ne_zero j)).symm.trans
      ((ht j).trans (hOther q j.succ (Fin.succ_ne_zero j))),hL⟩
  · rintro ⟨ht,hSame⟩
    have hL : (headKey (f p).val).2 = (headKey (f q).val).2 := by
      apply (headKey_labels_projection_iff σ hσ _ _).mpr
      rwa [hFactor,hFactor]
    apply Prod.ext
    · funext j
      exact (hOther p j.succ (Fin.succ_ne_zero j)).trans
        ((ht j).trans (hOther q j.succ (Fin.succ_ne_zero j)).symm)
    · exact hL

theorem surjective_head_factor_sameRV_kernel (f : Map A B) (hf : SpecialRelative f 0)
    (σ : Fin b → Fin l) (hσ : Function.Surjective σ) (d : Map A D)
    (hFactor : ∀ p : A, activeUnaryProjection 0 σ (f p).val = (d p).val) (p q : A) :
    SameRV (headKey (f p).val) (headKey (f q).val) ↔
      (∀ j : Fin n, rv (vfAt p.val j.succ) = rv (vfAt q.val j.succ)) ∧ SameRV (d p).val (d q).val := by
  have hOther := specialRelative_unaryRelative hf
  constructor
  · intro he
    obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp he
    have hL := (headKey_labels_projection_iff σ hσ (f p).val (f q).val).mp hl
    rw [hFactor,hFactor] at hL
    refine ⟨fun j => ?_,hL⟩
    exact (congrArg rv (hOther p j.succ (Fin.succ_ne_zero j))).symm.trans
      ((hv j).trans (congrArg rv (hOther q j.succ (Fin.succ_ne_zero j))))
  · rintro ⟨hv,hSame⟩
    have hL : (headKey (f p).val).2 = (headKey (f q).val).2 := by
      apply (headKey_labels_projection_iff σ hσ _ _).mpr
      rwa [hFactor,hFactor]
    apply (sameRV_iff _ _).mpr
    refine ⟨fun j => ?_,hL⟩
    exact (congrArg rv (hOther p j.succ (Fin.succ_ne_zero j))).trans
      ((hv j).trans (congrArg rv (hOther q j.succ (Fin.succ_ne_zero j))).symm)

theorem gammaPointIsoOfSurjectiveKernels_sameRV_iff
    {a c e v w : ℕ} {X : DefSet (M := M) S a c} {Y : DefSet (M := M) S n e} {Z : DefSet (M := M) S v w}
    (q : Map X Y) (hq : Function.Surjective q) (f : Map X Z) (hf : Function.Surjective f)
    (hker : ∀ a b : X, q a = q b ↔ f a = f b)
    (hqG : GammaGraphDefinable G (pointMapGraph q)) (hfG : GammaGraphDefinable G (pointMapGraph f))
    (hRV : ∀ a b : X, SameRV (q a).val (q b).val ↔ SameRV (f a).val (f b).val) (p r : Y) :
    SameRV ((gammaPointIsoOfSurjectiveKernels q hq f hf hker hqG hfG).equiv p).val
      ((gammaPointIsoOfSurjectiveKernels q hq f hf hker hqG hfG).equiv r).val ↔ SameRV p.val r.val := by
  obtain ⟨a,rfl⟩ := hq p
  obtain ⟨b,rfl⟩ := hq r
  rw [gammaPointIsoOfSurjectiveKernels_square,gammaPointIsoOfSurjectiveKernels_square]
  exact (hRV a b).symm

end IntegrationInACVF.Section5
