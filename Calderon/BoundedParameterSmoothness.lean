import Calderon.CommonSupportSlices
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.ContinuousMap.Bounded.Normed

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped BoundedContinuousFunction ContDiff Topology
universe u
namespace OAI.AnisotropicCalderon.BoundedParameterSmoothness

variable {V H E : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

instance (priority := 2000) instOperatorFieldNormedAddCommGroup :
    NormedAddCommGroup (V →ᵇ (H →L[ℝ] E)) := inferInstance

instance (priority := 2000) instOperatorFieldNormedSpace :
    NormedSpace ℝ (V →ᵇ (H →L[ℝ] E)) := inferInstance

def applyBoundedFamily (A : V →ᵇ (H →L[ℝ] E)) (h : H) : V →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => A x h)
    (A.continuous.clm_apply continuous_const) (‖A‖ * ‖h‖)
    (fun x => (A x).le_opNorm h |>.trans
      (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm x) (norm_nonneg h)))

lemma norm_applyBoundedFamily_le (A : V →ᵇ (H →L[ℝ] E)) (h : H) :
    ‖applyBoundedFamily A h‖ ≤ ‖A‖ * ‖h‖ := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (norm_nonneg A) (norm_nonneg h))).mpr
  intro x
  exact (A x).le_opNorm h |>.trans
    (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm x) (norm_nonneg h))

def transposeAt (A : V →ᵇ (H →L[ℝ] E)) : H →L[ℝ] (V →ᵇ E) :=
  ({toFun := applyBoundedFamily A
    map_add' := by intros; ext; simp [applyBoundedFamily]
    map_smul' := by intros; ext; simp [applyBoundedFamily]} : H →ₗ[ℝ] (V →ᵇ E)).mkContinuous
      ‖A‖ (norm_applyBoundedFamily_le A)

lemma transposeAt_apply (A : V →ᵇ (H →L[ℝ] E)) (h : H) (x : V) :
    transposeAt A h x = A x h := rfl

lemma norm_transposeAt_le (A : V →ᵇ (H →L[ℝ] E)) : ‖transposeAt A‖ ≤ ‖A‖ :=
  (transposeAt A).opNorm_le_bound (norm_nonneg A) (norm_applyBoundedFamily_le A)

def transposeBoundedFamily :
    (V →ᵇ (H →L[ℝ] E)) →L[ℝ] (H →L[ℝ] (V →ᵇ E)) := by
  let T : (V →ᵇ (H →L[ℝ] E)) →ₗ[ℝ] (H →L[ℝ] (V →ᵇ E)) :=
    { toFun := fun A => transposeAt (V := V) (H := H) (E := E) A
      map_add' := by intros; ext; simp [transposeAt_apply]
      map_smul' := by intros; ext; simp [transposeAt_apply] }
  have hb : ∀ A : V →ᵇ (H →L[ℝ] E), ‖T A‖ ≤ 1 * ‖A‖ := by
    intro A
    change ‖transposeAt A‖ ≤ 1 * ‖A‖
    simpa only [one_mul] using norm_transposeAt_le A
  exact LinearMap.mkContinuous (E := V →ᵇ (H →L[ℝ] E))
    (F := H →L[ℝ] (V →ᵇ E)) T 1 hb

lemma transposeBoundedFamily_apply (A : V →ᵇ (H →L[ℝ] E)) (h : H) (x : V) :
    transposeBoundedFamily A h x = A x h := rfl

theorem hasFDerivAt_of_uniform_slice_derivative
    (F : H → (V →ᵇ E)) (D : H → (V →ᵇ (H →L[ℝ] E))) (t : H)
    (hD : ContinuousAt D t)
    (hFD : ∀ y x, HasFDerivAt (fun z => F z x) (D y x) y) :
    HasFDerivAt F (transposeBoundedFamily (D t)) t := by
  apply HasFDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hev : ∀ᶠ y in 𝓝 t, ‖D y - D t‖ < ε := by
    have hs : ContinuousAt (fun y : H => D y - D t) t := hD.sub continuousAt_const
    have hn0 : ContinuousAt (fun A : V →ᵇ (H →L[ℝ] E) => ‖A‖) (D t - D t) :=
      (continuous_norm (E := V →ᵇ (H →L[ℝ] E))).continuousAt
    have hn : Tendsto (fun y => ‖D y - D t‖) (𝓝 t) (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def,sub_self,norm_zero] using
        (hn0.comp (f := fun y : H => D y - D t) (x := t) hs).tendsto
    exact hn.eventually (Iio_mem_nhds hε)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  filter_upwards [Metric.ball_mem_nhds t hδ] with y hy
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro x
  let g : H → E := fun z => F z x - F t x - D t x (z-t)
  have hgd (z : H) : HasFDerivAt g (D z x - D t x) z := by
    have hh : HasFDerivAt (fun w => D t x (w-t)) (D t x) z := by
      simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using
        (D t x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const t)
    change HasFDerivAt ((fun w => F w x - F t x) -
      fun w => D t x (w-t)) (D z x - D t x) z
    exact ((hFD z x).sub_const (F t x)).sub hh
  have hbound (z : H) (hz : z ∈ Metric.ball t δ) : ‖D z x - D t x‖ ≤ ε :=
    ((D z - D t).norm_coe_le_norm x).trans (hball hz).le
  have hg := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hgd z).hasFDerivWithinAt) hbound (convex_ball t δ)
    (Metric.mem_ball_self hδ) hy
  simpa [g,transposeBoundedFamily_apply,BoundedContinuousFunction.sub_apply] using hg

def basePartial (g : H × V → E) (z : H × V) : H →L[ℝ] E :=
  (fderiv ℝ g z).comp (ContinuousLinearMap.inl ℝ H V)

lemma hasFDerivAt_base_slice (g : H × V → E) (hg : Differentiable ℝ g)
    (t : H) (x : V) : HasFDerivAt (fun y => g (y,x)) (basePartial g (t,x)) t :=
  (hg (t,x)).hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)

lemma contDiff_basePartial (n : ℕ) (g : H × V → E) (hg : ContDiff ℝ (n+1) g) :
    ContDiff ℝ n (basePartial g) :=
  (ContinuousLinearMap.contDiff (𝕜 := ℝ)
    ((ContinuousLinearMap.compL ℝ H (H × V) E).flip
      (ContinuousLinearMap.inl ℝ H V))).comp (hg.fderiv_right (by simp))

lemma basePartial_zero_outside (g : H × V → E) (hg : Differentiable ℝ g)
    (K : Set V) (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    ∀ t x, x ∉ K → basePartial g (t,x) = 0 := by
  intro t x hx
  have he : (fun y : H => g (y,x)) = fun _ => (0 : E) :=
    funext (fun y => hz y x hx)
  have hzero : HasFDerivAt (fun y : H => g (y,x)) (0 : H →L[ℝ] E) t := by
    rw [he]
    exact hasFDerivAt_const (0 : E) t
  exact (hasFDerivAt_base_slice g hg t x).unique hzero

theorem contDiff_commonSupportSlice (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (g : H × V → E) (hg : ContDiff ℝ n g)
      (K : Set V) (hK : IsCompact K) (hz : ∀ t x, x ∉ K → g (t,x) = 0),
      ContDiff ℝ n (CommonSupportSlices.commonSupportSlice g hg.continuous K hK hz) := by
  induction n with
  | zero =>
      intro E _ _ g hg K hK hz
      exact contDiff_zero.mpr
        (CommonSupportSlices.continuous_commonSupportSlice g hg.continuous K hK hz)
  | succ n ih =>
      intro E _ _ g hg K hK hz
      have hp := contDiff_basePartial n g hg
      have hz' := basePartial_zero_outside g (hg.differentiable (by simp)) K hz
      have hDC := ih (H →L[ℝ] E) (basePartial g) hp K hK hz'
      have hT : ContDiff ℝ n (transposeBoundedFamily (V := V) (H := H) (E := E)) :=
        ContinuousLinearMap.contDiff _
      refine contDiff_succ_iff_hasFDerivAt.mpr
        ⟨fun t => transposeBoundedFamily
          (CommonSupportSlices.commonSupportSlice (basePartial g) hp.continuous K hK hz' t),
          hT.comp hDC,?_⟩
      intro t
      apply hasFDerivAt_of_uniform_slice_derivative
        (CommonSupportSlices.commonSupportSlice g hg.continuous K hK hz)
        (CommonSupportSlices.commonSupportSlice (basePartial g) hp.continuous K hK hz')
        t hDC.continuous.continuousAt
      intro y x
      exact hasFDerivAt_base_slice g (hg.differentiable (by simp)) y x

theorem contDiff_infty_commonSupportSlice (g : H × V → E) (hg : ContDiff ℝ ∞ g)
    (K : Set V) (hK : IsCompact K) (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    ContDiff ℝ ∞ (CommonSupportSlices.commonSupportSlice g hg.continuous K hK hz) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro n _
  exact contDiff_commonSupportSlice n E g (hg.of_le (by simp)) K hK hz

end OAI.AnisotropicCalderon.BoundedParameterSmoothness
