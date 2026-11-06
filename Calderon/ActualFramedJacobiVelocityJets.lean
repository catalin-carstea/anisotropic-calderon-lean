import Calderon.ReferenceFramedNormalizedEndpointIntegralIdentities
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Source-only candidate, fully expanded and typed before source.
No compiler/checker/axiom result is asserted. The actual center-horizontal
phase variation uses the negative metric connection; no quadratic jet is
assumed. All specializations retain the same supplied reference endpoint. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator NormalCoordinatesFrame

private instance instCompleteActualJacobiJetR3 : CompleteSpace R3 :=
  FiniteDimensional.complete ℝ R3

/-- The endpoint first derivative is locally constant along the open zero-velocity slice. -/
theorem fderiv_fderiv_endpoint_center_zero
    (Θ : R3 × R3 → R3) (hΘ : ContDiff ℝ ∞ Θ)
    (B : Set (R3 × R3)) (hB : IsOpen B)
    (hfirst : ∀ y, (y,0) ∈ B →
      HasFDerivAt Θ
        (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0))
    (y X : R3) (hy : (y,0) ∈ B) (h : R3 × R3) :
    fderiv ℝ (fderiv ℝ Θ) (y,0) (X,0) h = 0 := by
  let D : (R3 × R3) →L[ℝ] R3 :=
    ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3
  have hroom : ∀ᶠ x : R3 in 𝓝 y, (x,0) ∈ B :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually
      (hB.mem_nhds hy)
  have heq : (fun x : R3 => fderiv ℝ Θ (x,0)) =ᶠ[𝓝 y]
      (fun _ : R3 => D) := by
    filter_upwards [hroom] with x hx
    exact (hfirst x hx).fderiv
  have hD : ContDiff ℝ ∞ (fderiv ℝ Θ) := hΘ.fderiv_right (by simp)
  have hslice : HasFDerivAt (fun x : R3 => fderiv ℝ Θ (x,0))
      ((fderiv ℝ (fderiv ℝ Θ) (y,0)).comp
        (ContinuousLinearMap.inl ℝ R3 R3)) y :=
    (hD.differentiable (by simp) (y,0)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) y (0 : R3))
  have hz : fderiv ℝ (fun x : R3 => fderiv ℝ Θ (x,0)) y =
      fderiv ℝ (fun _ : R3 => D) y :=
    heq.fderiv_eq (𝕜 := ℝ)
  have hconst : fderiv ℝ (fun _ : R3 => D) y =
      (0 : R3 →L[ℝ] ((R3 × R3) →L[ℝ] R3)) :=
    fderiv_const_apply (𝕜 := ℝ) (x := y) D
  rw [hslice.fderiv,hconst] at hz
  have he := congrArg (fun A : R3 →L[ℝ] ((R3 × R3) →L[ℝ] R3) => A X h) hz
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.zero_apply] using he

/-- Smoothness supplies the required opposite ordering of the mixed Hessian. -/
theorem fderiv_fderiv_endpoint_center_zero_swap
    (Θ : R3 × R3 → R3) (hΘ : ContDiff ℝ ∞ Θ)
    (B : Set (R3 × R3)) (hB : IsOpen B)
    (hfirst : ∀ y, (y,0) ∈ B →
      HasFDerivAt Θ
        (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0))
    (y X : R3) (hy : (y,0) ∈ B) (h : R3 × R3) :
    fderiv ℝ (fderiv ℝ Θ) (y,0) h (X,0) = 0 := by
  have hs : IsSymmSndFDerivAt ℝ Θ (y,0) :=
    hΘ.contDiffAt.isSymmSndFDerivAt (by simp)
  rw [hs h (X,0)]
  exact fderiv_fderiv_endpoint_center_zero Θ hΘ B hB hfirst y X hy h

/-- Radial differentiation of the true phase derivative, with its initial parallel variation. -/
theorem hasDerivAt_endpoint_parallel_velocity_zero
    (Θ : R3 × R3 → R3) (hΘ : ContDiff ℝ ∞ Θ)
    (B : Set (R3 × R3)) (hB : IsOpen B)
    (hfirst : ∀ y, (y,0) ∈ B →
      HasFDerivAt Θ
        (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0))
    (y : R3) (hy : (y,0) ∈ B) (v E c : R3) :
    HasDerivAt (fun r : ℝ => fderiv ℝ Θ (y,r • v) (E,-r • c)) (-c) 0 := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ Θ) := hΘ.fderiv_right (by simp)
  have hc : HasDerivAt (fun r : ℝ => (y,r • v)) (0,v) 0 := by
    convert (hasDerivAt_const (0 : ℝ) y).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1 <;>
      simp only [id_eq,one_smul]
  have hDc : HasDerivAt (fun r : ℝ => fderiv ℝ Θ (y,r • v))
      (fderiv ℝ (fderiv ℝ Θ) (y,0) (0,v)) 0 := by
    exact (hD.differentiable (by simp) (y,0)).hasFDerivAt.comp_hasDerivAt_of_eq
      0 hc (by simp)
  have hi : HasDerivAt (fun r : ℝ => (E,-r • c)) (0,-c) 0 := by
    convert (hasDerivAt_const (0 : ℝ) E).prodMk
      ((hasDerivAt_id (0 : ℝ)).neg.smul_const c) using 1 <;>
      simp only [Pi.neg_apply,id_eq,neg_smul,one_smul]
  have hApplied : HasDerivAt (fun r : ℝ => fderiv ℝ Θ (y,r • v) (E,-r • c))
      (fderiv ℝ (fderiv ℝ Θ) (y,0) (0,v) (E,0) +
        fderiv ℝ Θ (y,0) (0,-c)) 0 := by
    convert hDc.clm_apply hi using 1 <;>
      first | rfl | simp only [zero_smul,neg_zero]
  have hm := fderiv_fderiv_endpoint_center_zero_swap Θ hΘ B hB hfirst y E hy (0,v)
  have hJet : fderiv ℝ (fderiv ℝ Θ) (y,0) (0,v) (E,0) +
      fderiv ℝ Θ (y,0) (0,-c) = -c := by
    rw [hm,(hfirst y hy).fderiv]
    simp only [add_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',zero_add]
  exact hApplied.congr_deriv hJet

/-- The actual spatial differential has the prescribed pure-velocity second derivative. -/
theorem hasDerivAt_endpoint_velocity_differential_zero
    (Θ : R3 × R3 → R3) (hΘ : ContDiff ℝ ∞ Θ) (y v E : R3) :
    HasDerivAt (fun r : ℝ => fderiv ℝ Θ (y,r • v) (0,E))
      (fderiv ℝ (fderiv ℝ Θ) (y,0) (0,v) (0,E)) 0 := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ Θ) := hΘ.fderiv_right (by simp)
  have hc : HasDerivAt (fun r : ℝ => (y,r • v)) (0,v) 0 := by
    convert (hasDerivAt_const (0 : ℝ) y).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1 <;>
      simp only [id_eq,one_smul]
  let A : ((R3 × R3) →L[ℝ] R3) →L[ℝ] R3 :=
    ContinuousLinearMap.apply ℝ R3 ((0 : R3),E)
  have hApply : HasFDerivAt (fun p : R3 × R3 => fderiv ℝ Θ p (0,E))
      (A.comp (fderiv ℝ (fderiv ℝ Θ) (y,0))) (y,0) :=
    A.hasFDerivAt.comp (y,0) (hD.differentiable (by simp) (y,0)).hasFDerivAt
  have hCurve : HasDerivAt (fun r : ℝ => fderiv ℝ Θ (y,r • v) (0,E))
      (A (fderiv ℝ (fderiv ℝ Θ) (y,0) (0,v))) 0 :=
    hApply.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  exact hCurve

/-- Literal physical center-horizontal endpoint variation. Its frame-coordinate
realization is the negative connection direction, proved in the companion source. -/
def referenceFramedCenterHorizontalVelocity (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (i : Fin 3) (a : ReferenceEndpointVariables) : R3 :=
  let F := conformalReferenceGramFrameOperatorJoint g L (a.1,a.2.1.1)
  let Γ := coordinateConnectionField
    (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L a.1)))
    (metricOperatorField (conformalReferenceMatrix g L a.1)) a.2.1.1
  fderiv ℝ (fun p => (Φ a.1 p 1).1)
    (a.2.1.1,a.2.1.2 • F a.2.2)
    (F (coordinateVector i),-a.2.1.2 • Γ (F (coordinateVector i)) (F a.2.2))

def referenceFramedCenterHorizontalResidual (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (i : Fin 3) (a : ReferenceEndpointVariables) : R3 :=
  referenceFramedCenterHorizontalVelocity g L Φ i a -
    referenceFramedNormalizedJacobian g L Φ a (coordinateVector i)

/-- Joint smoothness is proved from the actual phase derivative and actual reference data. -/
theorem contDiff_referenceFramedCenterHorizontalVelocity
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1)) (i : Fin 3) :
    ContDiff ℝ ∞ (referenceFramedCenterHorizontalVelocity g L Φ i) := by
  let Θ : ℝ × (R3 × R3) → R3 := fun p => (Φ p.1 p.2 1).1
  let M := conformalReferenceOperatorJoint g L
  let Q : ℝ × R3 → R3 →L[ℝ] R3 := fun p => Ring.inverse (M p)
  let F : ReferenceEndpointVariables → R3 →L[ℝ] R3 :=
    fun a => conformalReferenceGramFrameOperatorJoint g L (a.1,a.2.1.1)
  let Γ : ReferenceEndpointVariables → R3 →L[ℝ] R3 →L[ℝ] R3 :=
    fun a => parameterCoordinateConnectionField Q M (a.1,a.2.1.1)
  let E : ReferenceEndpointVariables → R3 := fun a => F a (coordinateVector i)
  let v : ReferenceEndpointVariables → R3 := fun a => F a a.2.2
  let T : ReferenceEndpointVariables → ℝ × (R3 × R3) :=
    fun a => (a.1,(a.2.1.1,a.2.1.2 • v a))
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_conformalReferenceGramFrameOperatorJoint g hg L).comp
      (contDiff_fst.prodMk contDiff_snd.fst.fst)
  have hΓ : ContDiff ℝ ∞ Γ :=
    (contDiff_parameterCoordinateConnectionField Q M
      (contDiff_conformalReferenceInverseJoint g hg L)
      (contDiff_conformalReferenceOperatorJoint g hg L)).comp
        (contDiff_fst.prodMk contDiff_snd.fst.fst)
  have hE : ContDiff ℝ ∞ E := hF.clm_apply contDiff_const
  have hv : ContDiff ℝ ∞ v := hF.clm_apply contDiff_snd.snd
  have hT : ContDiff ℝ ∞ T := contDiff_fst.prodMk
    (contDiff_snd.fst.fst.prodMk (contDiff_snd.fst.snd.smul hv))
  have hS : ContDiff ℝ ∞ (fun a : ReferenceEndpointVariables =>
      (E a,-a.2.1.2 • Γ a (E a) (v a))) :=
    hE.prodMk (contDiff_snd.fst.snd.neg.smul ((hΓ.clm_apply hE).clm_apply hv))
  have heq : referenceFramedCenterHorizontalVelocity g L Φ i =
      fun a => parameterPhaseDerivative Θ (T a) (E a,-a.2.1.2 • Γ a (E a) (v a)) := by
    funext a
    have hSlice : fderiv ℝ (fun w : R3 × R3 => Θ (a.1,w))
        (a.2.1.1,a.2.1.2 • v a) = parameterPhaseDerivative Θ (T a) :=
      fderiv_parameter_endpoint_slice Θ hΘ a.1 (a.2.1.1,a.2.1.2 • v a)
    change fderiv ℝ (fun w : R3 × R3 => Θ (a.1,w))
      (a.2.1.1,a.2.1.2 • v a) (E a,-a.2.1.2 • Γ a (E a) (v a)) =
        parameterPhaseDerivative Θ (T a) (E a,-a.2.1.2 • Γ a (E a) (v a))
    exact congrArg (fun A : (R3 × R3) →L[ℝ] R3 =>
      A (E a,-a.2.1.2 • Γ a (E a) (v a))) hSlice
  rw [heq]
  exact ((contDiff_parameterPhaseDerivative Θ hΘ).comp hT).clm_apply hS

theorem contDiff_referenceFramedCenterHorizontalResidual
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1)) (i : Fin 3) :
    ContDiff ℝ ∞ (referenceFramedCenterHorizontalResidual g L Φ i) :=
  (contDiff_referenceFramedCenterHorizontalVelocity g hg L Φ hΘ i).sub
    ((contDiff_referenceFramedNormalizedJacobian g hg L Φ hΘ).clm_apply contDiff_const)

/-- Derived zero and first radial jets; no desired Jacobi remainder is a hypothesis. -/
theorem referenceFramedCenterHorizontalResidual_zero_radialJet
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
    (hData : ConformalReferenceGeodesicEndpointData g L y0 Φ B)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : (y,0) ∈ B)
    (z : R3) (i : Fin 3) :
    referenceFramedCenterHorizontalResidual g L Φ i (q,((y,0),z)) = 0 ∧
    HasDerivAt (fun r : ℝ =>
      referenceFramedCenterHorizontalResidual g L Φ i (q,((y,r),z))) 0 0 := by
  rcases hData with ⟨hB,_,_,_,_,_,_,hΘ,_,hfirst,hsecond⟩
  let Θ : R3 × R3 → R3 := fun p => (Φ q p 1).1
  let F := conformalReferenceGramFrameOperatorJoint g L (q,y)
  let E := F (coordinateVector i)
  let v := F z
  let Γ := coordinateConnectionField
    (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
    (metricOperatorField (conformalReferenceMatrix g L q)) y
  let c := Γ E v
  have hΘq : ContDiff ℝ ∞ Θ := hΘ.comp (contDiff_const.prodMk contDiff_id)
  have hf : ∀ x, (x,0) ∈ B →
      HasFDerivAt Θ
        (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (x,0) :=
    fun x hx => hfirst q hq x hx
  have hK : HasDerivAt (fun r : ℝ =>
      referenceFramedCenterHorizontalVelocity g L Φ i (q,((y,r),z))) (-c) 0 :=
    hasDerivAt_endpoint_parallel_velocity_zero Θ hΘq B hB hf y hy v E c
  have hJraw := hasDerivAt_endpoint_velocity_differential_zero Θ hΘq y v E
  have hH : fderiv ℝ (fderiv ℝ Θ) (y,0) (0,v) (0,E) = -c := by
    change fderiv ℝ (fderiv ℝ (fun p : R3 × R3 => (Φ q p 1).1))
      (y,0) (0,v) (0,E) = -Γ E v
    exact hsecond q hq y hy E v
  have hJfun : (fun r : ℝ =>
      referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)) (coordinateVector i)) =
      (fun r : ℝ => fderiv ℝ Θ (y,r • v) (0,E)) := by
    funext r
    rfl
  have hJ : HasDerivAt (fun r : ℝ =>
      referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)) (coordinateVector i)) (-c) 0 := by
    rw [hJfun]
    exact hJraw.congr_deriv hH
  refine ⟨?_,?_⟩
  · have hThetaZero : fderiv ℝ Θ (y,0) (E,0) = E := by
      rw [(hf y hy).fderiv]
      simp only [add_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',add_zero]
    have hKzero : referenceFramedCenterHorizontalVelocity g L Φ i (q,((y,0),z)) = E := by
      change fderiv ℝ Θ (y,(0 : ℝ) • v) (E,-(0 : ℝ) • c) = E
      simpa only [zero_smul,neg_zero] using hThetaZero
    have hJzero : referenceFramedNormalizedJacobian g L Φ (q,((y,0),z))
        (coordinateVector i) = E := by
      rw [referenceFramedNormalizedJacobian_zero g L Φ q y z (hf y hy)]
    change referenceFramedCenterHorizontalVelocity g L Φ i (q,((y,0),z)) -
      referenceFramedNormalizedJacobian g L Φ (q,((y,0),z)) (coordinateVector i) = 0
    rw [hKzero,hJzero,sub_self]
  · change HasDerivAt (fun r : ℝ =>
      referenceFramedCenterHorizontalVelocity g L Φ i (q,((y,r),z)) -
        referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)) (coordinateVector i)) 0 0
    exact (hK.sub hJ).congr_deriv (sub_self (-c))

end OAI.AnisotropicCalderon.ConnectionError
