import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace OAI.AnisotropicCalderon.CommonSupportSlices

variable {H V E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma slice_norm_bounded (g : H × V → E) (hg : Continuous g)
    (K : Set V) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) :
    ∃ C : ℝ, ∀ x, ‖g (t,x)‖ ≤ C := by
  have hc : Continuous (fun x : V => g (t,x)) :=
    hg.comp (continuous_const.prodMk continuous_id)
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max 0 B,fun x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hB x hx).trans (le_max_right _ _)
  · rw [hz t x hx, norm_zero]
    exact le_max_left _ _

def commonSupportSlice (g : H × V → E) (hg : Continuous g)
    (K : Set V) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) : V →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => g (t,x))
    (hg.comp (continuous_const.prodMk continuous_id))
    (Classical.choose (slice_norm_bounded g hg K hK hz t))
    (Classical.choose_spec (slice_norm_bounded g hg K hK hz t))

lemma commonSupportSlice_apply (g : H × V → E) (hg : Continuous g)
    (K : Set V) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) (x : V) :
    commonSupportSlice g hg K hK hz t x = g (t,x) := rfl

def compactSupportRestriction (g : H × V → E) (hg : Continuous g)
    (K : Set V) (t : H) : C(K,E) :=
  ⟨fun x => g (t,x.val),hg.comp (continuous_const.prodMk continuous_subtype_val)⟩

lemma compactSupportRestriction_apply (g : H × V → E) (hg : Continuous g)
    (K : Set V) (t : H) (x : K) :
    compactSupportRestriction g hg K t x = g (t,x.val) := rfl

lemma norm_slice_sub_le_restriction_sub (g : H × V → E) (hg : Continuous g)
    (K : Set V) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t u : H) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ‖commonSupportSlice g hg K hK hz t - commonSupportSlice g hg K hK hz u‖ ≤
      ‖compactSupportRestriction g hg K t - compactSupportRestriction g hg K u‖ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro x
  by_cases hx : x ∈ K
  · exact (compactSupportRestriction g hg K t - compactSupportRestriction g hg K u).norm_coe_le_norm ⟨x,hx⟩
  · change ‖g (t,x) - g (u,x)‖ ≤ _
    rw [hz t x hx,hz u x hx,sub_self,norm_zero]
    exact norm_nonneg _

theorem continuous_commonSupportSlice (g : H × V → E) (hg : Continuous g)
    (K : Set V) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    Continuous (commonSupportSlice g hg K hK hz) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (compactSupportRestriction g hg K) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hg.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp hc.continuousAt ε hε
  refine ⟨δ,hδ,fun {u} hu => ?_⟩
  rw [dist_eq_norm]
  exact (norm_slice_sub_le_restriction_sub g hg K hK hz u t).trans_lt
    (by simpa only [dist_eq_norm] using hd hu)

end OAI.AnisotropicCalderon.CommonSupportSlices
