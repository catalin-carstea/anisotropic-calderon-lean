import Calderon.FramedNormalizedEndpoint
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ConnectionError

/-- Source: exact framed normalized endpoint definitions and inner identity.
Expansion: EXPANSION-v001.md E1. Status: UNCOMPILED author proposal. -/
theorem framedNormalizedEndpointMetric_eq_gram
    (Θ : R3 × R3 → R3) (M F : R3 → R3 →L[ℝ] R3) (p : (R3 × ℝ) × R3) :
    framedNormalizedEndpointMetric Θ M F p =
      (framedNormalizedEndpointDerivative Θ F p).adjoint.comp
        ((M (framedScaledEndpoint Θ F p)).comp (framedNormalizedEndpointDerivative Θ F p)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  change inner ℝ (framedNormalizedEndpointMetric Θ M F p u) v =
    inner ℝ ((framedNormalizedEndpointDerivative Θ F p).adjoint
      (M (framedScaledEndpoint Θ F p) (framedNormalizedEndpointDerivative Θ F p u))) v
  rw [framedNormalizedEndpointMetric_inner,ContinuousLinearMap.adjoint_inner_left]

/-- Source: elementary kernel argument; no premise on invertibility of J.
Expansion: EXPANSION-v001.md E2. Status: UNCOMPILED author proposal. -/
theorem injective_of_positive_gram_lower_bound
    (J A : R3 →L[ℝ] R3) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ u : R3, c * ‖u‖ ^ 2 ≤ inner ℝ (A (J u)) (J u)) :
    Function.Injective J := by
  intro u v huv
  have hJ : J (u-v) = 0 := by rw [map_sub,huv,sub_self]
  have hh : c * ‖u-v‖ ^ 2 ≤ 0 := by
    simpa only [hJ,map_zero,inner_zero_left] using hbound (u-v)
  have hz : u-v = 0 := by
    by_contra hn
    have hp : 0 < c * ‖u-v‖ ^ 2 := mul_pos hc (pow_pos (norm_pos_iff.mpr hn) 2)
    exact (not_lt_of_ge hh) hp
  exact sub_eq_zero.mp hz

/-- Source: pinned finite-dimensional surjectivity and continuous linear equivalence APIs.
Expansion: EXPANSION-v001.md E2. Status: UNCOMPILED author proposal. -/
theorem isInvertible_of_injective_endomorphism (J : R3 →L[ℝ] R3)
    (hJ : Function.Injective J) : J.IsInvertible := by
  have hbij : Function.Bijective J.toLinearMap :=
    ⟨hJ,J.toLinearMap.surjective_of_injective hJ⟩
  refine ⟨(LinearEquiv.ofBijective J.toLinearMap hbij).toContinuousLinearEquiv,?_⟩
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- Source: actual framedNormalizedEndpointMetric_inner, specialized to the literal J and E.
Expansion: EXPANSION-v001.md E3. Status: UNCOMPILED author proposal. -/
theorem framedNormalizedEndpointDerivative_injective_of_lower_bound
    (Θ : R3 × R3 → R3) (M F : R3 → R3 →L[ℝ] R3) (p : (R3 × ℝ) × R3)
    (c : ℝ) (hc : 0 < c)
    (hbound : ∀ u : R3, c * ‖u‖ ^ 2 ≤ inner ℝ (framedNormalizedEndpointMetric Θ M F p u) u) :
    Function.Injective (framedNormalizedEndpointDerivative Θ F p) := by
  apply injective_of_positive_gram_lower_bound (framedNormalizedEndpointDerivative Θ F p)
    (M (framedScaledEndpoint Θ F p)) c hc
  intro u
  simpa only [framedNormalizedEndpointMetric_inner] using hbound u

/-- Source: nonzero real scalar cancellation and finite-dimensional injection/surjection.
Expansion: EXPANSION-v001.md E3. Status: UNCOMPILED author proposal. -/
theorem smul_isInvertible_of_injective_endomorphism (J : R3 →L[ℝ] R3)
    (hJ : Function.Injective J) (r : ℝ) (hr : r ≠ 0) : (r • J).IsInvertible := by
  apply isInvertible_of_injective_endomorphism
  intro u v huv
  apply hJ
  have hscaled : r • J u = r • J v := huv
  have hcancel := congrArg (fun w : R3 => r⁻¹ • w) hscaled
  simpa only [smul_smul,inv_mul_cancel₀ hr,one_smul] using hcancel

/-- Source: pinned ContDiff inverse theorem, openness of operator invertibility, and restrOpen.
Expansion: EXPANSION-v001.md E4. Status: UNCOMPILED author proposal. -/
theorem exists_smooth_local_chart_of_isInvertible_fderiv (f : R3 → R3)
    (hf : ContDiff ℝ ∞ f) (z : R3) (hD : (fderiv ℝ f z).IsInvertible) :
    ∃ e : OpenPartialHomeomorph R3 R3,
      (e : R3 → R3) = f ∧ z ∈ e.source ∧ f z ∈ e.target ∧
      ContDiffOn ℝ ∞ f e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨D,hDeq⟩ := hD
  have hfd : HasFDerivAt f (D : R3 →L[ℝ] R3) z := by
    rw [hDeq]
    exact (hf.differentiable (by simp) z).hasFDerivAt
  let e0 := hf.contDiffAt.toOpenPartialHomeomorph f hfd (by simp)
  let U : Set R3 := {x | (fderiv ℝ f x).IsInvertible}
  have hU : IsOpen U := by
    exact ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
      (hf.fderiv_right (m := ∞) (by simp)).continuous
  let e := e0.restrOpen U hU
  have heq : (e : R3 → R3) = f := rfl
  have hsource : e.source = e0.source ∩ U := e0.restrOpen_source U hU
  have hz : z ∈ e.source := by
    rw [hsource]
    exact ⟨hf.contDiffAt.mem_toOpenPartialHomeomorph_source hfd (by simp),⟨D,hDeq⟩⟩
  refine ⟨e,heq,hz,?_,hf.contDiffOn,?_⟩
  · exact e.map_source hz
  · intro q hq
    have hx : e.symm q ∈ e.source := e.map_target hq
    have hxU : e.symm q ∈ U := (hsource ▸ hx).2
    obtain ⟨Dq,hDq⟩ := hxU
    have hdq : HasFDerivAt e (Dq : R3 →L[ℝ] R3) (e.symm q) := by
      change HasFDerivAt f (Dq : R3 →L[ℝ] R3) (e.symm q)
      rw [hDq]
      exact (hf.differentiable (by simp) (e.symm q)).hasFDerivAt
    have hsq : ContDiffAt ℝ ∞ e.symm q :=
      e.contDiffAt_symm hq hdq hf.contDiffAt
    exact hsq.contDiffWithinAt

/-- Source: actual framed metric lower bound, exact physical slice derivative and pinned IFT.
Expansion: EXPANSION-v001.md E3-E4. Status: UNCOMPILED author proposal. -/
theorem exists_framedScaledEndpoint_local_chart_of_lower_bound
    (Θ : R3 × R3 → R3) (M F : R3 → R3 →L[ℝ] R3)
    (hΘ : ContDiff ℝ ∞ Θ) (y z : R3) (r c : ℝ) (hr : r ≠ 0) (hc : 0 < c)
    (hbound : ∀ u : R3, c * ‖u‖ ^ 2 ≤
      inner ℝ (framedNormalizedEndpointMetric Θ M F ((y,r),z) u) u) :
    Function.Injective (framedNormalizedEndpointDerivative Θ F ((y,r),z)) ∧
    (framedNormalizedEndpointDerivative Θ F ((y,r),z)).IsInvertible ∧
    HasFDerivAt (fun w => Θ (y,r • F y w))
      (r • framedNormalizedEndpointDerivative Θ F ((y,r),z)) z ∧
    (r • framedNormalizedEndpointDerivative Θ F ((y,r),z)).IsInvertible ∧
    ∃ e : OpenPartialHomeomorph R3 R3,
      (e : R3 → R3) = (fun w => Θ (y,r • F y w)) ∧
      z ∈ e.source ∧ Θ (y,r • F y z) ∈ e.target ∧
      ContDiffOn ℝ ∞ (fun w => Θ (y,r • F y w)) e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  have hJ := framedNormalizedEndpointDerivative_injective_of_lower_bound Θ M F ((y,r),z) c hc hbound
  have hJI := isInvertible_of_injective_endomorphism _ hJ
  have hphys := smul_isInvertible_of_injective_endomorphism _ hJ r hr
  have hfd := hasFDerivAt_framedScaledEndpoint_slice Θ F hΘ y z r
  refine ⟨hJ,hJI,hfd,hphys,?_⟩
  have hs : ContDiff ℝ ∞ (fun w : R3 => r • F y w) :=
    (F y).contDiff.const_smul r
  have hf : ContDiff ℝ ∞ (fun w : R3 => Θ (y,r • F y w)) :=
    hΘ.comp (contDiff_const.prodMk hs)
  apply exists_smooth_local_chart_of_isInvertible_fderiv _ hf z
  rw [hfd.fderiv]
  exact hphys

end OAI.AnisotropicCalderon.ConnectionError
