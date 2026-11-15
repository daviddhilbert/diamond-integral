import IntegrationSection5.RVProjectionPadding
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5.RVProjectionPadding
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S R : Set M} {a b c : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b} {C : DefSet (M := M) S 1 c}
variable {ρ : Fin a → Fin b} {σ : Fin b → Fin c}

def extendBase (P : RVProjectionPadding (G := G) B A ρ) (h : S ⊆ R) :
    RVProjectionPadding (G := G) (SpecialTransformations.Section5.extendBase B h)
      (SpecialTransformations.Section5.extendBase A h) ρ where
  iso := P.iso
  values p := P.values ⟨p.val,p.property⟩
  sameRV p q := P.sameRV ⟨p.val,p.property⟩ ⟨q.val,q.property⟩

def castTarget {A' : DefSet (M := M) S 1 a} (P : RVProjectionPadding (G := G) B A ρ)
    (h : A = A') : RVProjectionPadding (G := G) B A' ρ := by cases h; exact P

def castSource {B' : DefSet (M := M) S 1 b} (P : RVProjectionPadding (G := G) B A ρ)
    (h : B = B') : RVProjectionPadding (G := G) B' A ρ := by cases h; exact P

def trans (P : RVProjectionPadding (G := G) B A ρ) (Q : RVProjectionPadding (G := G) C B σ) :
    RVProjectionPadding (G := G) C A (σ ∘ ρ) where
  iso := Q.iso.trans (gammaLogicInput G) P.iso
  values p := by
    change (P.iso.equiv (Q.iso.equiv p)).val = _
    rw [P.values,Q.values]
    rfl
  sameRV p q := (P.sameRV (Q.iso.equiv p) (Q.iso.equiv q)).trans (Q.sameRV p q)

end IntegrationInACVF.Section5.RVProjectionPadding
