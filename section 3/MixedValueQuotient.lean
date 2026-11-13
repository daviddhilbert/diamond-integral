import Mathlib.Data.Set.Prod
import Mathlib.Data.Finset.Basic
set_option autoImplicit false
namespace DiamondIntegral.Section3
variable {R T V : Type}

def mixedValueProjection (v : T → V) (x : R × T) : R × V := (x.1,v x.2)

def mixedValueQuotient (v : T → V) (A : Set (R × T)) : Set (R × V) := mixedValueProjection v '' A

theorem mixedValueQuotient_mem (v : T → V) (A : Set (R × T)) (r : R) (γ : V) :
    (r,γ) ∈ mixedValueQuotient v A ↔ ∃ t, (r,t) ∈ A ∧ v t = γ := by
  constructor
  · rintro ⟨⟨s,t⟩,hst,he⟩
    have hs : s = r := congrArg Prod.fst he
    have ht : v t = γ := congrArg Prod.snd he
    exact ⟨t,hs ▸ hst,ht⟩
  · rintro ⟨t,ht,he⟩
    exact ⟨(r,t),ht,Prod.ext rfl he⟩

/-- Angular fibre invariance recovers the literal full preimage of the
mixed residue/value quotient. No representatives are selected. -/
theorem mixedValueQuotient_full_preimage (v : T → V) (A : Set (R × T))
    (h : ∀ r t u, (r,t) ∈ A → v t = v u → (r,u) ∈ A) :
    mixedValueProjection v ⁻¹' mixedValueQuotient v A = A := by
  ext ⟨r,t⟩
  change (r,v t) ∈ mixedValueQuotient v A ↔ (r,t) ∈ A
  rw [mixedValueQuotient_mem]
  exact ⟨fun ⟨u,hu,he⟩ => h r u t hu he,fun ht => ⟨t,ht,rfl⟩⟩

theorem mixedValueProjection_preimage_prod (v : T → V) (W : Set R) (I : Set V) :
    mixedValueProjection v ⁻¹' (W ×ˢ I) = W ×ˢ (v ⁻¹' I) := rfl

theorem mixedValueQuotient_rectangles (v : T → V) (A : Set (R × T))
    (h : ∀ r t u, (r,t) ∈ A → v t = v u → (r,u) ∈ A)
    (P : Finset (Set R)) (I : Set R → Set V)
    (hrect : ∀ r γ, (r,γ) ∈ mixedValueQuotient v A ↔ ∃ W ∈ P, r ∈ W ∧ γ ∈ I W) :
    ∀ r t, (r,t) ∈ A ↔ ∃ W ∈ P, r ∈ W ∧ t ∈ v ⁻¹' I W := by
  intro r t
  have he := Set.ext_iff.mp (mixedValueQuotient_full_preimage v A h) (r,t)
  exact he.symm.trans (hrect r (v t))
end DiamondIntegral.Section3
