import Calderon.SpatialJetFields
import Calderon.CompactRadialRemainder
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Topology ContDiff BigOperators

namespace OAI.AnisotropicCalderon.ConnectionError

variable {E V P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def fixedDirectionalDerivative (F : E → V) (v : E) (x : E) : V :=
  fderiv ℝ F x v

theorem contDiff_fixedDirectionalDerivative (F : E → V) (hF : ContDiff ℝ ∞ F) (v : E) :
    ContDiff ℝ ∞ (fixedDirectionalDerivative F v) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- Genuine interchange of two fixed directions, derived from smooth real calculus. -/
theorem fixedDirectionalDerivative_commute (F : E → V) (hF : ContDiff ℝ ∞ F) (v w : E) :
    fixedDirectionalDerivative (fixedDirectionalDerivative F v) w =
      fixedDirectionalDerivative (fixedDirectionalDerivative F w) v := by
  funext x
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  change (fderiv ℝ (fun y => fderiv ℝ F y v) x) w =
    (fderiv ℝ (fun y => fderiv ℝ F y w) x) v
  rw [fderiv_clm_apply hDF (differentiableAt_const v),
    fderiv_clm_apply hDF (differentiableAt_const w)]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using
    ((hF.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)).eq w v

/-- A word of actual fixed directional derivatives, ordered as `iteratedFDeriv`. -/
def fixedJetEval : (j : ℕ) → (Fin j → E) → (E → V) → E → V
  | 0, _, F => F
  | j + 1, m, F =>
      fixedDirectionalDerivative (fixedJetEval j (Fin.tail m) F) (m 0)

theorem contDiff_fixedJetEval (j : ℕ) (m : Fin j → E) (F : E → V)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (fixedJetEval j m F) := by
  induction j with
  | zero => simpa only [fixedJetEval] using hF
  | succ j ih =>
      exact contDiff_fixedDirectionalDerivative _ (ih (Fin.tail m)) (m 0)

theorem fixedJetEval_eq_iteratedFDeriv (j : ℕ) (m : Fin j → E) (F : E → V)
    (hF : ContDiff ℝ ∞ F) :
    fixedJetEval j m F = fun x => iteratedFDeriv ℝ j F x m := by
  induction j with
  | zero =>
      funext x
      simp only [fixedJetEval, iteratedFDeriv_zero_apply]
  | succ j ih =>
      rw [fixedJetEval, ih (Fin.tail m)]
      funext x
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j F) x :=
        (hF.iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp) x
      exact (hd.iteratedFDeriv_succ_apply_left' (m := m)).symm

/-- Move one fixed derivative through an arbitrary finite derivative word. -/
theorem fixedDirectionalDerivative_fixedJetEval (j : ℕ) (m : Fin j → E)
    (F : E → V) (hF : ContDiff ℝ ∞ F) (v : E) :
    fixedDirectionalDerivative (fixedJetEval j m F) v =
      fixedJetEval j m (fixedDirectionalDerivative F v) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [fixedJetEval]
      rw [fixedDirectionalDerivative_commute _ (contDiff_fixedJetEval j (Fin.tail m) F hF)
        (m 0) v, ih (Fin.tail m)]

/-- The actual jet in all nonradial variables; radial slots are excluded. -/
def parameterJetField (j : ℕ) (F : P × ℝ → V) (x : P × ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => P) V :=
  (iteratedFDeriv ℝ j F x).compContinuousLinearMap
    (fun _ => ContinuousLinearMap.inl ℝ P ℝ)

theorem contDiff_parameterJetField (j : ℕ) (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (parameterJetField j F) := by
  unfold parameterJetField
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin j => ContinuousLinearMap.inl ℝ P ℝ))).comp
        (hF.iteratedFDeriv_right (m := ∞) (by simp))

theorem parameterJetField_eq_iteratedFDeriv (j : ℕ) (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (p : P) (r : ℝ) :
    parameterJetField j F (p,r) = iteratedFDeriv ℝ j (fun q => F (q,r)) p := by
  have hc : ContDiff ℝ ∞ (fun z : P × ℝ => F ((0,r) + z)) :=
    hF.comp (contDiff_const.add contDiff_id)
  have he : (fun q : P => F (q,r)) =
      (fun z : P × ℝ => F ((0,r) + z)) ∘ ContinuousLinearMap.inl ℝ P ℝ := by
    funext q
    simp
  rw [he, (ContinuousLinearMap.inl ℝ P ℝ).iteratedFDeriv_comp_right hc p (by simp)]
  rw [iteratedFDeriv_comp_add_left]
  simp [parameterJetField]

theorem parameterJetField_apply_eq_fixedJetEval (j : ℕ) (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (m : Fin j → P) :
    (fun x => parameterJetField j F x m) =
      fixedJetEval j (fun i => (m i,0)) F := by
  rw [fixedJetEval_eq_iteratedFDeriv j _ F hF]
  funext x
  simp only [parameterJetField, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.inl_apply]

/-- All finite parameter jets commute with the actual radial derivative.
    This is a proved field equality, not a mixed-jet premise. -/
theorem radialFirstDerivative_parameterJetField (j : ℕ) (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) :
    radialFirstDerivative (parameterJetField j F) =
      parameterJetField j (radialFirstDerivative F) := by
  funext x
  ext m
  have hJ : DifferentiableAt ℝ (parameterJetField j F) x :=
    (contDiff_parameterJetField j F hF).differentiable (by simp) x
  calc
    radialFirstDerivative (parameterJetField j F) x m =
        fixedDirectionalDerivative (fun y => parameterJetField j F y m) (0,1) x := by
      symm
      exact fderiv_continuousMultilinear_apply_const_apply hJ m (0,1)
    _ = fixedDirectionalDerivative (fixedJetEval j (fun i => (m i,0)) F) (0,1) x := by
      rw [parameterJetField_apply_eq_fixedJetEval j F hF m]
    _ = fixedJetEval j (fun i => (m i,0)) (radialFirstDerivative F) x := by
      change fixedDirectionalDerivative (fixedJetEval j (fun i => (m i,0)) F) (0,1) x =
        fixedJetEval j (fun i => (m i,0)) (fixedDirectionalDerivative F (0,1)) x
      rw [fixedDirectionalDerivative_fixedJetEval j _ F hF (0,1)]
    _ = parameterJetField j (radialFirstDerivative F) x m :=
      (congrFun (parameterJetField_apply_eq_fixedJetEval j _
        (contDiff_radialFirstDerivative F hF) m) x).symm

/-- Literal slice equalities yield jet equalities on the closure of an open parameter set. -/
theorem parameterJetField_eq_on_closure (j : ℕ) (F G : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (s : Set P) (hs : IsOpen s)
    (r : ℝ) (heq : ∀ p ∈ s, F (p,r) = G (p,r)) :
    ∀ p ∈ closure s, parameterJetField j F (p,r) = parameterJetField j G (p,r) := by
  have he : EqOn (fun p => parameterJetField j F (p,r))
      (fun p => parameterJetField j G (p,r)) s := by
    intro p hp
    change parameterJetField j F (p,r) = parameterJetField j G (p,r)
    rw [parameterJetField_eq_iteratedFDeriv j F hF p r,
      parameterJetField_eq_iteratedFDeriv j G hG p r]
    have hlocal : (fun q : P => F (q,r)) =ᶠ[𝓝 p] (fun q : P => G (q,r)) := by
      filter_upwards [hs.mem_nhds hp] with q hq
      exact heq q hq
    exact (hlocal.iteratedFDeriv ℝ j).eq_of_nhds
  exact he.closure
    ((contDiff_parameterJetField j F hF).continuous.comp
      (continuous_id.prodMk continuous_const))
    ((contDiff_parameterJetField j G hG).continuous.comp
      (continuous_id.prodMk continuous_const))

/-- Differentiate a locally zero radial-zero slice, then extend by continuity to closure. -/
theorem parameterJetField_zero_on_closure (j : ℕ) (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (s : Set P) (hs : IsOpen s)
    (hzero : ∀ p ∈ s, F (p,0) = 0) :
    ∀ p ∈ closure s, parameterJetField j F (p,0) = 0 := by
  have hz : EqOn (fun p => parameterJetField j F (p,0)) (fun _ => 0) s := by
    intro p hp
    change parameterJetField j F (p,0) = 0
    rw [parameterJetField_eq_iteratedFDeriv j F hF p 0]
    have he : (fun q : P => F (q,0)) =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [hs.mem_nhds hp] with q hq
      exact hzero q hq
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
      (he.iteratedFDeriv ℝ j).eq_of_nhds
  exact hz.closure
    ((contDiff_parameterJetField j F hF).continuous.comp
      (continuous_id.prodMk continuous_const)) continuous_const

/-- A radial derivative slice with its literal derivative vector. -/
theorem hasDerivAt_radialSlice (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) (p : P) (r : ℝ) :
    HasDerivAt (fun t : ℝ => F (p,t)) (radialFirstDerivative F (p,r)) r := by
  have hc : HasDerivAt (fun t : ℝ => (p,t)) (0,1) r :=
    (hasDerivAt_const r p).prodMk (hasDerivAt_id r)
  exact (hF.differentiable (by simp) (p,r)).hasFDerivAt.comp_hasDerivAt r hc

/-- The zero radial derivative propagates to parameter jets and to the boundary. -/
theorem hasDerivAt_parameterJetField_zero_on_closure (j : ℕ) (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (s : Set P) (hs : IsOpen s)
    (hzero : ∀ p ∈ s, HasDerivAt (fun t : ℝ => F (p,t)) 0 0) :
    ∀ p ∈ closure s, HasDerivAt (fun r : ℝ => parameterJetField j F (p,r)) 0 0 := by
  have hz : ∀ p ∈ s, radialFirstDerivative F (p,0) = 0 := by
    intro p hp
    rw [← deriv_radialSlice F hF p 0, (hzero p hp).deriv]
  have hJzero := parameterJetField_zero_on_closure j (radialFirstDerivative F)
    (contDiff_radialFirstDerivative F hF) s hs hz
  intro p hp
  have hd := hasDerivAt_radialSlice (parameterJetField j F)
    (contDiff_parameterJetField j F hF) p 0
  rw [radialFirstDerivative_parameterJetField j F hF, hJzero p hp] at hd
  exact hd

/-- One chosen signed compact cylinder works at every finite jet order.
    The hypotheses concern only the zeroth value and zeroth radial derivative. -/
theorem exists_compact_uniform_parameterJet_quadratic_bound
    (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) (s q : Set P)
    (hs : IsOpen s) (hq : IsCompact q) (hqs : q ⊆ closure s)
    (hzero : ∀ p ∈ s, F (p,0) = 0)
    (hjet : ∀ p ∈ s, HasDerivAt (fun t : ℝ => F (p,t)) 0 0)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N →
      ∀ p ∈ q, ∀ r : ℝ, |r| ≤ δ → ‖parameterJetField j F (p,r)‖ ≤ C * r^2 := by
  have hsingle (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ q, ∀ r : ℝ, |r| ≤ δ → ‖parameterJetField j F (p,r)‖ ≤ C * r^2 := by
    obtain ⟨C,hC,hbound⟩ := exists_compact_uniform_radial_quadratic_bound
      (parameterJetField j F) (contDiff_parameterJetField j F hF) q hq δ hδ
      (fun p hp => hasDerivAt_parameterJetField_zero_on_closure j F hF s hs hjet p (hqs hp))
    refine ⟨C,hC,?_⟩
    intro p hp r hr
    simpa only [parameterJetField_zero_on_closure j F hF s hs hzero p (hqs hp), sub_zero] using
      hbound p hp r hr
  choose C hC hbound using hsingle
  intro N
  refine ⟨∑ k ∈ Finset.range (N+1), C k,
    Finset.sum_nonneg (fun k _ => hC k), ?_⟩
  intro j hj p hp r hr
  have hmem : j ∈ Finset.range (N+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hle : C j ≤ ∑ k ∈ Finset.range (N+1), C k :=
    Finset.single_le_sum (fun k _ => hC k) hmem
  exact (hbound j p hp r hr).trans (mul_le_mul_of_nonneg_right hle (sq_nonneg r))

end OAI.AnisotropicCalderon.ConnectionError
