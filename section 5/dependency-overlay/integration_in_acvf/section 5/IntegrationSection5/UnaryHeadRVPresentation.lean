import IntegrationSection5.RVProjectionNormalization
import IntegrationSection5.RVUnaryProfiles
import IntegrationSection5.RVContractionMaps

/-! The RV domain after contracting the final unary head is exactly the
actual key domain of its prepared unary target. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m k : ℕ}

theorem unary_head_key_labels (V : DefSet (M := M) S 1 m) (a : V) :
    (headKeyMap V a).val.2 = (rawKeyMap V a).val := by
  rw [headKeyMap_apply,rawKeyMap_apply]
  funext j
  cases j using Fin.addCases with
  | left j => fin_cases j; rfl
  | right j => simp only [headKey,Fin.append_right]

theorem unary_head_raw_domain (V : DefSet (M := M) S 1 m) :
    carrier (Map.image (rawLabelMap (headImage V))) = carrier (Map.image (rawKeyMap V)) := by
  ext z
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨a,ha⟩ := b.property
    refine ⟨a,?_⟩
    have h := congrArg Prod.snd ha
    exact (unary_head_key_labels V a).symm.trans (h.trans hb)
  · rintro ⟨a,ha⟩
    exact ⟨Map.toImage (headKeyMap V) a,(unary_head_key_labels V a).trans ha⟩

def unaryHeadVolumeIso (V : DefSet (M := M) S 1 m) (ρ : Fin k → Fin (1+m)) :
    selectedVolumeObject (Map.image (rawLabelMap (headImage V))) ρ ≅
      selectedVolumeObject (Map.image (rawKeyMap V)) ρ :=
  @SpecialTransformations.Section4.rvIsoOfCarrierEq M (@CanonicalStructure.normalize M sM) S k (1+m)
    (Map.image (rawLabelMap (headImage V))) (Map.image (rawKeyMap V))
    (rawRVProjectionMap ρ _) (rawRVProjectionMap ρ _) (unary_head_raw_domain V) (fun _ => rfl)

theorem special_target_constant_label {a b : ℕ} {A : DefSet (M := M) S 1 a}
    {B : DefSet (M := M) S 1 b} (T : SpecialBijection A B)
    (j : Fin a) (r : RV (M := M)) (hr : ∀ p : A, p.val.2 j = r) (q : B) :
    q.val.2 (suffixIndex (special_chain_rvArity_le T.chain) j) = r := by
  obtain ⟨p,rfl⟩ := T.bijective.2 q
  exact (special_oldLabels T p j).trans (hr p)

theorem unary_profile_projection (V : DefSet (M := M) S 1 m)
    (j : Fin m) (r : RV (M := M)) (hr : ∀ p : V, p.val.2 j = r)
    (ρ : Fin 2 → Fin (1+m))
    (hρ0 : ρ 0 = Fin.natAdd 1 j) (hρ1 : ρ 1 = 0)
    (a : rvObjectDomain (pullbackObject V)) :
    (rawRVProjectionMap ρ (Map.image (rawKeyMap V)) a).val =
      ![r,(rvObjectVolume (pullbackObject V) a).val 0] := by
  obtain ⟨p,rfl⟩ := rawKeyImage_surjective V a
  funext i
  fin_cases i
  · change (rawKeyMap V p).val (ρ 0) = r
    rw [hρ0,rawKeyMap_apply,Fin.append_right]
    exact hr p
  · change (rawKeyMap V p).val (ρ 1) = (rawKeyMap V p).val (Fin.castAdd m 0)
    rw [hρ1]
    apply congrArg (rawKeyMap V p).val
    exact Fin.ext rfl

end IntegrationInACVF.Section5
