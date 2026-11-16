import «section 6».RVIndexedRVRowBounds
import «section 6».DefinableSurjectiveDescent
import «section 6».RegularizedLoci

/-! Complete powerset-valued RV rows descend through an actual
surjective definable map. Constancy and separate row bounds on a
doubly bounded RV quotient give one original-base named bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}
variable {P : SpecialTransformations.DefinableGeometry.Space LRV M}
variable {A : DefSet P S} {B : DefSet (rawRVSpace (M := M) n) S}

def descendedRVRowRelation (q : Map A B) (R : P.Carrier → (Fin m → RVInfinity M) → Prop)
    (b : Fin n → RVInfinity M) (u : Fin m → RVInfinity M) : Prop :=
  ∃ a : A,(q a).val=b ∧ R a.val u

theorem descendedRVRowRelation_definable
    (q : Map A B) (R : P.Carrier → (Fin m → RVInfinity M) → Prop)
    (hR : P.RelationDefinable (rawRVSpace m) S R) :
    (rawRVSpace n).RelationDefinable (rawRVSpace m) S (descendedRVRowRelation q R) := by
  have hComp := (q.graph_definable.swap P (rawRVSpace n)).comp (rawRVSpace n) P (rawRVSpace m) hR
  apply hComp.congr (rawRVSpace n) (rawRVSpace m)
  intro b u
  constructor
  · rintro ⟨x,⟨a,rfl,hq⟩,hR⟩
    exact ⟨a,hq,hR⟩
  · rintro ⟨a,hq,hR⟩
    exact ⟨a.val,⟨a,rfl,hq⟩,hR⟩

theorem descendedRVRowRelation_at
    (q : Map A B) (R : P.Carrier → (Fin m → RVInfinity M) → Prop)
    (hSame : ∀ a b : A,(q a).val=(q b).val → ∀ u,R a.val u ↔ R b.val u) (a : A) :
    {u | descendedRVRowRelation q R (q a).val u}={u | R a.val u} := by
  ext u
  constructor
  · rintro ⟨b,hb,hR⟩
    exact (hSame b a hb u).mp hR
  · intro hR
    exact ⟨a,rfl,hR⟩

theorem raw_rv_relation_at
    (R : (Fin n → RVInfinity M) → (Fin m → RVInfinity M) → Prop)
    (b : Fin n → RVInfinity M) (u : Fin m → RVInfinity M) :
    Sum.elim (rvValues b) (rvValues u) ∈ (rawRVSpace n).relation (rawRVSpace m) R ↔ R b u := by
  have h := (rawRVSpace (M := M) n).relation_decode (rawRVSpace m) R
    ⟨rvValues b,⟨b,rfl⟩⟩ ⟨rvValues u,⟨u,rfl⟩⟩
  simpa only [decode_rvValues] using h

theorem definable_rv_row_descent_named_bound
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (q : Map A B) (hq : Function.Surjective q) (hB : RVValueDoublyBounded B.carrier)
    (R : P.Carrier → (Fin m → RVInfinity M) → Prop) (hR : P.RelationDefinable (rawRVSpace m) S R)
    (hSame : ∀ a b : A,(q a).val=(q b).val → ∀ u,R a.val u ↔ R b.val u)
    (hRows : ∀ a : A,RVValueDoublyBounded {u | R a.val u}) :
    ∃ δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      ∀ a : A,∀ u,R a.val u → ∀ i,(δ⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ δ.val := by
  let D := rvValues '' B.carrier
  have hD : S.Definable LRV D := (rv_definable_iff_values_image S B.carrier).mp B.definable
  have hNZ : ∀ x ∈ D,∀ i,GammaParameters.NonzeroRV (x i) := by
    rintro x ⟨b,hb,rfl⟩ i
    exact ⟨(b i).property,fun he => hB.nonzero b hb i (Subtype.ext he)⟩
  have hDB : RVCodeDoublyBounded D := by
    obtain ⟨γ,hγ⟩ := hB
    refine ⟨γ,?_⟩
    rintro x ⟨b,hb,rfl⟩ i
    change (γ⁻¹).val ≤ (GammaParameters.codeValue (b i).val).val ∧
      (GammaParameters.codeValue (b i).val).val ≤ γ.val
    rw [nonzero_rv_codeValue_val (b i) (RVValueDoublyBounded.nonzero ⟨γ,hγ⟩ b hb i)]
    exact hγ b hb i
  let G := (rawRVSpace n).relation (rawRVSpace m) (descendedRVRowRelation q R)
  have hG : S.Definable LRV G := descendedRVRowRelation_definable q R hR
  have hGRows : ∀ x ∈ D,RVValueDoublyBounded {u : Fin m → RVInfinity M | Sum.elim x (rvValues u) ∈ G} := by
    rintro x ⟨b,hb,rfl⟩
    obtain ⟨a,ha⟩ := hq ⟨b,hb⟩
    have haV : (q a).val=b := congrArg Subtype.val ha
    have hRow : {u : Fin m → RVInfinity M | Sum.elim (rvValues b) (rvValues u) ∈ G}={u | R a.val u} := by
      ext u
      change Sum.elim (rvValues b) (rvValues u) ∈
        (rawRVSpace n).relation (rawRVSpace m) (descendedRVRowRelation q R) ↔ R a.val u
      rw [raw_rv_relation_at,← haV]
      exact Set.ext_iff.mp (descendedRVRowRelation_at q R hSame a) u
    rw [hRow]
    exact hRows a
  obtain ⟨δ,hδ,hBound⟩ := rv_indexed_rv_rows_named_bound hc h00 linear hκ hs hsmall hΓ D hD hNZ hDB G hG hGRows
  refine ⟨δ,hδ,?_⟩
  intro a u hu i
  apply hBound (rvValues (q a).val) ⟨(q a).val,(q a).property,rfl⟩ u _ i
  exact (raw_rv_relation_at _ _ _).mpr ⟨a,rfl,hu⟩

end DiamondIntegral.Section6
