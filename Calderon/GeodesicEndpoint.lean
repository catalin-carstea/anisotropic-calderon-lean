import Calderon.GeodesicSprayLinearization
import Calderon.SmoothFlowLinearization

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ContDiff Topology NNReal
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hasFDerivAt_stationary_zeroVelocity_endpoint (v : E × E → E × E)
    {K : ℝ≥0} (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) (y : E)
    (hz : v (y,0) = 0)
    (hD : fderiv ℝ v (y,0) = zeroVelocityLinearization) :
    HasFDerivAt (fun z => (ODE.globalSolution v hv z 1).1)
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y,0) := by
  let F : (E × E) × ℝ → E × E := fun p => ODE.globalSolution v hv p.1 p.2
  have hF : ContDiff ℝ ∞ F := contDiff_infty_globalSolution v hv hvs
  have hphase : ContDiff ℝ ∞ (fun z => F (z,1)) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  have hp := (hphase.differentiable (by simp) (y,0)).hasFDerivAt
  have hθ := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp (y,0) hp
  have heq : (ContinuousLinearMap.fst ℝ E E).comp
      (fderiv ℝ (fun z => F (z,1)) (y,0)) =
      ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E := by
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.comp_apply, fderiv_base_slice F hF (y,0) w 1]
    change (fderiv ℝ F ((y,0),1) (w,0)).1 = w.1 + w.2
    have hn : ∀ w, fderiv ℝ v (y,0) (fderiv ℝ v (y,0) w) = 0 := by
      intro w
      rw [hD]
      exact zeroVelocityLinearization_nilpotent w
    have hj := globalSolution_baseDerivative_nilpotent v hv hvs (y,0) hz hn w 1
    simpa only [F, hD, one_smul, zeroVelocityLinearization_apply,
      Prod.fst_add] using congrArg Prod.fst hj
  exact hθ.congr_fderiv heq

variable [FiniteDimensional ℝ E]

theorem exists_smooth_coordinate_spray_endpoint (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) (y0 : E) :
    ∃ (Φ : (E × E) → ℝ → E × E) (A : Set (E × E)),
      IsOpen A ∧ (y0,0) ∈ A ∧
      ContDiff ℝ ∞ (fun p : (E × E) × ℝ => Φ p.1 p.2) ∧
      (∀ z, Φ z 0 = z) ∧
      (∀ y, (y,0) ∈ A → ∀ t, Φ (y,0) t = (y,0)) ∧
      (∀ z ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (Φ z) (geodesicPhaseField Q M (Φ z t)) t) ∧
      ContDiff ℝ ∞ (fun z => (Φ z 1).1) ∧
      ∀ y, (y,0) ∈ A → HasFDerivAt (fun z => (Φ z 1).1)
        (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y,0) := by
  let a : E × E := (y0,0)
  have hs : ContDiffOn ℝ (∞ + 1) (geodesicPhaseField Q M) univ := by
    simpa using (contDiff_geodesicPhaseField Q M hQ hM).contDiffOn
  obtain ⟨v,K,hvs,hv,heq⟩ :=
    hs.exists_lipschitzWith_contDiff_eventuallyEq_of_finiteDimensional
      (x := a) (by simp)
  have hvs' : ContDiff ℝ ∞ v := by simpa using hvs
  have hz : v a = 0 := by
    rw [heq.self_of_nhds]
    exact geodesicPhaseField_zero_velocity Q M y0
  have hstat := globalSolution_stationary v hv a hz
  have hF := contDiff_infty_globalSolution v hv hvs'
  obtain ⟨U,hUeq,hU,haU⟩ := mem_nhds_iff.mp heq
  have hopen : IsOpen ((fun p : (E × E) × ℝ =>
      ODE.globalSolution v hv p.1 p.2) ⁻¹' U) := hU.preimage hF.continuous
  have hsub : ({a} : Set (E × E)) ×ˢ Icc (0 : ℝ) 1 ⊆
      (fun p : (E × E) × ℝ => ODE.globalSolution v hv p.1 p.2) ⁻¹' U := by
    intro p hp
    change ODE.globalSolution v hv p.1 p.2 ∈ U
    rw [show p.1 = a from hp.1,hstat]
    exact haU
  obtain ⟨A,T,hA,_,haA,hIT,hAT⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hopen hsub
  have hAU : A ⊆ U := by
    intro z hzA
    have hx := hAT (a := (z,0)) ⟨hzA,hIT (by simp)⟩
    simpa only [mem_preimage, ODE.globalSolution_zero] using hx
  have hzero (y : E) (hy : (y,0) ∈ A) : v (y,0) = 0 := by
    rw [hUeq (hAU hy)]
    exact geodesicPhaseField_zero_velocity Q M y
  refine ⟨ODE.globalSolution v hv,A,hA,haA (mem_singleton a),hF,
    ODE.globalSolution_zero v hv,
    fun y hy => globalSolution_stationary v hv (y,0) (hzero y hy),?_,?_,?_⟩
  · intro z hzA t ht
    have hpos : ODE.globalSolution v hv z t ∈ U := hAT (a := (z,t)) ⟨hzA,hIT ht⟩
    rw [← hUeq hpos]
    exact ODE.hasDerivAt_globalSolution v hv z t
  · exact contDiff_fst.comp (hF.comp (contDiff_id.prodMk contDiff_const))
  · intro y hy
    have hlocal : v =ᶠ[𝓝 (y,0)] geodesicPhaseField Q M := by
      filter_upwards [hU.mem_nhds (hAU hy)] with z hzU
      exact hUeq hzU
    have hD : fderiv ℝ v (y,0) = zeroVelocityLinearization :=
      hlocal.fderiv_eq.trans (fderiv_geodesicPhaseField_zero_velocity Q M hQ hM y)
    exact hasFDerivAt_stationary_zeroVelocity_endpoint v hv hvs' y (hzero y hy) hD

end OAI.AnisotropicCalderon.ConnectionError
