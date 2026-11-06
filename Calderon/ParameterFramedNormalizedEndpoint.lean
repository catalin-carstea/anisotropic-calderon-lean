import Calderon.FramedNormalizedEndpoint
import Calderon.CompactRadialRemainder
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Constructions.SumProd

/-! The metric below is the literal native metric of the frozen-parameter endpoint. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Restrict the joint endpoint derivative to actual phase directions. -/
def parameterPhaseDerivative (Θ : P × (R3 × R3) → R3)
    (p : P × (R3 × R3)) : (R3 × R3) →L[ℝ] R3 :=
  (fderiv ℝ Θ p).comp (ContinuousLinearMap.inr ℝ P (R3 × R3))

theorem fderiv_parameter_endpoint_slice (Θ : P × (R3 × R3) → R3)
    (hΘ : ContDiff ℝ ∞ Θ) (q : P) (z : R3 × R3) :
    fderiv ℝ (fun w => Θ (q,w)) z = parameterPhaseDerivative Θ (q,z) := by
  exact ((hΘ.differentiable (by simp) (q,z)).hasFDerivAt.comp z
    (hasFDerivAt_prodMk_right q z)).fderiv

theorem contDiff_parameterPhaseDerivative (Θ : P × (R3 × R3) → R3)
    (hΘ : ContDiff ℝ ∞ Θ) : ContDiff ℝ ∞ (parameterPhaseDerivative Θ) :=
  (hΘ.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

/-- Literal fixed-parameter framed normalized metric, including radius zero. -/
def parameterFramedNormalizedEndpointMetric (Θ : P × (R3 × R3) → R3)
    (M F : P × R3 → R3 →L[ℝ] R3) (p : P × ((R3 × ℝ) × R3)) : R3 →L[ℝ] R3 :=
  framedNormalizedEndpointMetric (fun z => Θ (p.1,z))
    (fun y => M (p.1,y)) (fun y => F (p.1,y)) p.2

theorem contDiff_parameterFramedNormalizedEndpointMetric
    (Θ : P × (R3 × R3) → R3) (M F : P × R3 → R3 →L[ℝ] R3)
    (hΘ : ContDiff ℝ ∞ Θ) (hM : ContDiff ℝ ∞ M) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (parameterFramedNormalizedEndpointMetric Θ M F) := by
  let A : P × ((R3 × ℝ) × R3) → R3 →L[ℝ] R3 := fun p => F (p.1,p.2.1.1)
  let T : P × ((R3 × ℝ) × R3) → P × (R3 × R3) :=
    fun p => (p.1,(p.2.1.1,p.2.1.2 • A p p.2.2))
  let J : P × ((R3 × ℝ) × R3) → R3 →L[ℝ] R3 :=
    fun p => (parameterPhaseDerivative Θ (T p)).comp (ContinuousLinearMap.inr ℝ R3 R3)
  have hA : ContDiff ℝ ∞ A := hF.comp (contDiff_fst.prodMk contDiff_snd.fst.fst)
  have hT : ContDiff ℝ ∞ T := contDiff_fst.prodMk
    (contDiff_snd.fst.fst.prodMk
      (contDiff_snd.fst.snd.smul (hA.clm_apply contDiff_snd.snd)))
  have hJ : ContDiff ℝ ∞ J :=
    ((contDiff_parameterPhaseDerivative Θ hΘ).comp hT).clm_comp contDiff_const
  have hB : ContDiff ℝ ∞ (fun p => M (p.1,Θ (T p))) :=
    hM.comp (contDiff_fst.prodMk (hΘ.comp hT))
  have hAdj : ContDiff ℝ ∞ (fun L : R3 →L[ℝ] R3 => L.adjoint) :=
    (ContinuousLinearMap.adjoint : (R3 →L[ℝ] R3) ≃ₗᵢ[ℝ] (R3 →L[ℝ] R3)).contDiff
  have heq : parameterFramedNormalizedEndpointMetric Θ M F =
      fun p => (A p).adjoint.comp (((J p).adjoint.comp ((M (p.1,Θ (T p))).comp (J p))).comp (A p)) := by
    funext p
    unfold parameterFramedNormalizedEndpointMetric framedNormalizedEndpointMetric
      normalizedEndpointMetric normalizedEndpointDerivative framedEndpointParameter scaledEndpoint
    simp only [fderiv_parameter_endpoint_slice Θ hΘ]
    rfl
  rw [heq]
  exact (hAdj.comp hA).clm_comp
    (((hAdj.comp hJ).clm_comp (hB.clm_comp hJ)).clm_comp hA)

/-- One tube covers all compact frame parameters and spatial points. -/
theorem exists_commonRadius_parameter_framed_phase_domain
    (B : Set (R3 × R3)) (hB : IsOpen B) (y0 : R3) (hbase : (y0,0) ∈ B)
    (F : P × R3 → R3 →L[ℝ] R3) (hF : Continuous F)
    (K : Set P) (hK : IsCompact K) (Z : Set R3) (hZ : IsCompact Z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ K, ∀ y, ‖y-y0‖ ≤ ε →
      ∀ r : ℝ, |r| ≤ ε → ∀ z ∈ Z, (y,r • F (q,y) z) ∈ B := by
  let T : (R3 × ℝ) × (P × R3) → R3 × R3 :=
    fun p => (p.1.1,p.1.2 • F (p.2.1,p.1.1) p.2.2)
  have hT : Continuous T := continuous_fst.fst.prodMk
    (continuous_fst.snd.smul
      ((hF.comp (continuous_snd.fst.prodMk continuous_fst.fst)).clm_apply continuous_snd.snd))
  have ho : IsOpen (T ⁻¹' B) := hB.preimage hT
  have hsub : ({(y0,0)} : Set (R3 × ℝ)) ×ˢ (K ×ˢ Z) ⊆ T ⁻¹' B := by
    intro p hp
    change (p.1.1,p.1.2 • F (p.2.1,p.1.1) p.2.2) ∈ B
    rw [show p.1 = (y0,0) from hp.1]
    simpa only [zero_smul] using hbase
  obtain ⟨U,V,hU,_,h0,hKV,hUV⟩ :=
    generalized_tube_lemma isCompact_singleton (hK.prod hZ) ho hsub
  obtain ⟨a,ha,hball⟩ := Metric.isOpen_iff.mp hU (y0,0) (h0 (mem_singleton (y0,0)))
  refine ⟨a/2,by positivity,?_⟩
  intro q hq y hy r hr z hz
  have hp : (y,r) ∈ U := by
    apply hball
    rw [Metric.mem_ball,dist_eq_norm]
    change max ‖y-y0‖ ‖r-(0 : ℝ)‖ < a
    apply max_lt
    · exact lt_of_le_of_lt hy (half_lt_self ha)
    · simpa only [sub_zero,Real.norm_eq_abs] using lt_of_le_of_lt hr (half_lt_self ha)
  exact hUV (a := ((y,r),(q,z))) ⟨hp,hKV ⟨hq,hz⟩⟩

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The compact room is fixed before any finite derivative order. -/
theorem exists_compact_uniform_iteratedFDeriv_bound (G : E → V)
    (hG : ContDiff ℝ ∞ G) (S : Set E) (hS : IsCompact S) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ S,
      ‖iteratedFDeriv ℝ j G p‖ ≤ C := by
  have hsingle (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S,
      ‖iteratedFDeriv ℝ j G p‖ ≤ C := by
    obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn
      (hG.iteratedFDeriv_right (i := j) (m := ∞) (by simp)).continuous.continuousOn
    exact ⟨max C 0,le_max_right _ _,fun p hp => (hC p hp).trans (le_max_left _ _)⟩
  choose C hC hb using hsingle
  intro N
  refine ⟨∑ j ∈ Finset.range (N+1), C j,Finset.sum_nonneg (fun j _ => hC j),?_⟩
  intro j hj p hp
  have hmem : j ∈ Finset.range (N+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  exact (hb j p hp).trans (Finset.single_le_sum (fun k _ => hC k) hmem)

end OAI.AnisotropicCalderon.ConnectionError
